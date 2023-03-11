/*

SAT SOLVER

Author: Ang Ray Yan

Functionality Overview (Relevant resource links in code):
- Conflict Driven Clause Learning (CDCL) Algorithm
- Basic preprocessing: Existing unit clauses and pure literal detection
- 2 Watch Literals structure for Unit Propagation
- Recursive clause minimization on learnt 1-UIP clause
- Learning Rate Branching (LRB) Heuristic (with reason-side rate + locality extension)
- Literal block distance (LBD) computation
- Luby (Sequence) Restart
- Clause reduction: keep LBD <= 4, clause subsumption test (no self-subsumption)

Abbreviations used (if any):
* Lit (Literal)      - A variable or the negation of a variable
* Asgmt (Assignment) - A combination of a literal and true/false value
* Var (Variable)     - A symbol that represents an object. Can be assigned true or false
* Dec (Decision)     - The current decision made by CDCL algorithm on true/false value of literals
* WL (Watch Literal) - A literal in a clause that when turned false, will trigger unit propagation on the other
* (UN)SAT            - (UN)Satisfied (i.e. all (UN)true, be it variable / clause / entire CNF formula)
*/

#include <algorithm>
#include <cstdlib>
#include <ctime>
#include <fstream>
#include <iostream>
#include <sstream>
#include <unordered_map>
#include <unordered_set>
#include <utility>
#include <vector>

using namespace std;

// ------------------------------ 1 DEFINITIONS / STRUCTS ------------------------------

#define ENABLE_RANDOM false
#define DEBUG false

#define TERNARY(p, b1, b2) ((p) ? (b1) : (b2))

#define INVALID_LIT 0
#define INVALID_CLAUSE_INDEX (1 << 30)
#define INVALID_DEC_INDEX (1 << 30)

#define CLAUSE_UNKNOWN 0
#define CLAUSE_UNKNOWN_UNIT 1
#define CLAUSE_SATISFIED 2
#define CLAUSE_UNSATISFIED 3

#define LRB_ALPHA_INITIAL_VALUE 0.4
#define LRB_DECAY_RATE 0.95
#define LRB_ALPHA_DECAY 0.000001
#define LRB_ALPHA_MIN 0.06

// 1 = positive, 0 = negative
typedef unsigned Lit;
#define LIT_MAKE(x, y) (((x) << 1) + (int)(y))
#define LIT_NEG(x) ((x) ^ 1)
#define LIT_SIGN(x) ((x) & 1)
#define LIT_VAR(x) ((x) >> 1)


// Learing Rate Branching (LRB) Statistics implemented with Reason Side Rate (RSR) and locality extension
// Source: https://cs.uwaterloo.ca/~ppoupart/publications/sat/learning-rate-branching-heuristic-SAT.pdf
typedef struct {
    double value;                       // EMA (exp. Moving Average) value associated with ERWA algo. for MAB
    unsigned assigned;                  // learntCounter value when variable was assigned
    unsigned participatedOrReasoned;    // participated: incremented whenever variable participated in
                                        //               generating conflict / part of learnt clause
                                        // reasoned: number of learnt clauses v reasoned since assigned(v)
} LRBVarStats;

typedef struct {
    double alpha;
    unsigned learntCounter;
    vector<LRBVarStats> varStats;
} LRBStats;

// Source: https://hal-univ-artois.archives-ouvertes.fr/hal-03299473/document (On the Glucose SAT Solver)
typedef struct {
    Lit lastSATLit;                         // Last known assignment satisfying clause
    vector<Lit> lits;                       // List of literals in the clause
    Lit WL[2];                              // 2x Watch Literals for this clause
    short LBD;                              // Literal Block Distance (LBD) - not expecting to exceed "short" MAX value
} Clause;

typedef struct _Decision {
    Lit lit;
    unsigned decLevel;          // Value of decision level when this decision was made
    unsigned decTrailIndex;     // Index of decision in the decision trail
    unsigned reasonClauseIndex; // Index of clause that induced this decision (e.g. due to unit prop)
} Decision;

#define INVALID_DECISION ((Decision) { INVALID_LIT, 0, 0, INVALID_CLAUSE_INDEX })

// Common structures used by all parts of the algorithm
// Note: for STL vector, refrain from using pop_back() to achieve performance (time) improvement
typedef struct {
    unsigned numGeneratedUnitClauses;           // Number of unit clauses generated from conflicts
    bool isSAT;                                 // Final result: SAT = 1 (or UNSAT = 0)
    unsigned numVars;                           // Number of variables
    unsigned numDecisions;                      // Number of decisions made ("size" of VALID decTrail)
    unsigned litArraySize;                      // Size of any array storing information about literals (both +/-)
    unsigned numGivenClauses;                   // Number of given clauses
    unsigned numCoreClauses;                    // Number of core clauses (given + learnt clauses to not delete)
    unsigned decLevel;                          // Decision level (up to # of literals, 0 for unit clauses)
    unsigned conflictsSinceRestart;             // # of conflicts since last restart
    pair<unsigned, unsigned> lubyRestart;       // Luby sequence generator for restarts
    vector<Decision> decMap;                    // Stores a mapping of decision object (by index) for each VARIABLE (if any)
    vector<Lit> decTrail;                       // All non unit clause decisions (LITERAL) made in chronological order
    vector<Clause> clauses;                     // All the clauses
    vector<vector<unsigned> > twoWL;            // 2-watch literal structure (clause index)
    LRBStats lrb;                               // LRB statistics for CDCL solving
    Lit tempLit;                                // Placeholder, Store any literal for subsequent use (e.g. new watch literal etc.)
} Context;

// ------------------------------ 2 DEBUGGING / OUTPUT FUNCTIONS ------------------------------

void displayLit(Lit lit) {
    cout << TERNARY(LIT_SIGN(lit), "", "-") << LIT_VAR(lit);
}

void displayClause(Context* ctx, unsigned clauseIndex) {
    cout << "( ";
    Clause* clause = &ctx->clauses[clauseIndex];
    for (unsigned i = 0; i < clause->lits.size(); i++) {
        displayLit(clause->lits[i]);
        cout << " ";
    }
    cout << "<" << TERNARY(clauseIndex < ctx->numGivenClauses, "G ", "L ");
    displayLit(clause->WL[0]); cout << " "; displayLit(clause->WL[1]);
    cout << "> LBD:" << clause->LBD << ")";
}

void displayDecisions(Context* ctx) {
    cout << "\nc Decisions (Level 0 reason clauses may be absent):\nc ---------------";
    for (int i = 0; i < ctx->numDecisions; i++) {
        Decision dec = ctx->decMap[LIT_VAR(ctx->decTrail[i])];
        bool newDecLevel = i == 0 || (dec.decLevel != ctx->decMap[LIT_VAR(ctx->decTrail[i - 1])].decLevel);
        if (newDecLevel) cout << endl << "c Level #" << dec.decLevel << ": ";
        if (dec.reasonClauseIndex != INVALID_CLAUSE_INDEX) cout << " ->";
        else cout << endl << "c [!]";
        cout << " ("; displayLit(dec.lit); cout << ")";
        if (dec.reasonClauseIndex != INVALID_CLAUSE_INDEX) {
            cout << " [#" << dec.reasonClauseIndex << " - ";
            displayClause(ctx, dec.reasonClauseIndex);
            cout << "]";
        }
    }
    cout << endl;
}

// ------------------------------ 3 DIMACS FORMAT I/O ------------------------------

bool readDimacs(char* filename, Context* ctx) {
    // Open stream to read CNF file
    ifstream cnfFile(filename);
    if (!cnfFile) return false;
    // Process CNF file (read number of literals/clauses)
    string token = "";
    while (token.compare("cnf") != 0) cnfFile >> token;
    cnfFile >> ctx->numVars >> ctx->numGivenClauses;
    // Initialize context (assume SAT first until proven otherwise)
    ctx->isSAT = true;
    ctx->decLevel = 0;
    ctx->numGeneratedUnitClauses = 0;
    ctx->numDecisions = 0;
    ctx->litArraySize = (ctx->numVars + 1) << 1;
    ctx->numCoreClauses = ctx->numGivenClauses;
    ctx->lubyRestart = make_pair(1, 1);
    // Note: important to reserve size. Prevent invalid pointers + maintain cache efficiency
    ctx->clauses.resize(ctx->numGivenClauses);
    ctx->decTrail.resize(ctx->numVars + 1);
    ctx->decMap.resize(ctx->numVars + 1, INVALID_DECISION);
    ctx->twoWL.resize(ctx->litArraySize);
    // Process literals and clauses
    for (unsigned i = 0; i < ctx->numGivenClauses; i++) {
        Clause* clause = &ctx->clauses[i];
        clause->lastSATLit = INVALID_LIT;
        clause->WL[0] = INVALID_LIT;
        clause->WL[1] = INVALID_LIT;
        clause->LBD = 0;
        int lit;
        while (true) {
            cnfFile >> lit;
            if (lit == 0) break;
            clause->lits.push_back(LIT_MAKE(TERNARY(lit > 0, lit, -lit), lit > 0));
        }
        // Setup 2-WL structure (maybe random or not)
        for (unsigned j = 0, index; j < 2; j++) {
            if (clause->lits.size() <= j) break;
            // Locate a watch literal candidate (possibly at random)
            do {
                index = TERNARY(ENABLE_RANDOM, rand() % clause->lits.size(), j);
            } while (j > 0 && clause->lits[index] != clause->WL[0]);
            // Make it one
            ctx->twoWL[clause->lits[index]].push_back(i);
            clause->WL[j] = clause->lits[index];
        }
    }
    cnfFile.close();
    // Done
    return true;
}

void writeDimacs(Context* ctx) {
    // UNSAT - Indicate so
    if (!ctx->isSAT) {
        cout << "s UNSATISFIABLE" << endl;
        return;
    }
    // SAT - Print Solution
    displayDecisions(ctx);
    cout << "s SATISFIABLE" << endl;
    cout << "v ";
    for (unsigned i = 1; i <= ctx->numVars; i++) {
        displayLit(ctx->decMap[i].lit); cout << " ";
        if (i % 20 == 0 && i < ctx->numVars) cout << endl << "v ";
    }
    cout << endl;
}

// ------------------------------ 4 CLAUSE MINIMIZATION ------------------------------

bool isMarked(Context* ctx, unsigned initialVar, unsigned currentVar, vector<bool>* marked, vector<bool>* visited) {
    // If visited, use the marked value
    if ((*visited)[currentVar]) return (*marked)[currentVar];
    (*visited)[currentVar] = true;
    // Found something that is already marked
    if (initialVar != currentVar && (*marked)[currentVar]) return true;
     // If no reason clause exists, cannot check for marked literals, not subsumed
    unsigned newReasonClauseIndex = ctx->decMap[currentVar].reasonClauseIndex;
    if (newReasonClauseIndex == INVALID_CLAUSE_INDEX || ctx->decMap[currentVar].decLevel == 0) return false;
    // Otherwise, continue searching based on reason clause
    Clause* newReasonClause = &ctx->clauses[newReasonClauseIndex];
    bool result = true;
    for (unsigned j = 0; j < newReasonClause->lits.size(); j++) {
        // https://www.researchgate.net/publication/220944584_Minimizing_Learned_Clauses
        // Expecting about 30% less literals generated total --> speeds up unit prop. during clause checking for LARGER problems
        // Check if literal in reason clause is marked or not (1 is not marked = currentVar is not marked)
        // (1) Local clause minimization
        //result = result && (*marked)[newReasonClause->lits[j]];
        // (2) Recursive clause minimization
        result = result && isMarked(ctx, initialVar, LIT_VAR(newReasonClause->lits[j]), marked, visited);
    }
    // All reason clause literals marked = mark current variable ("caching" of sorts)
    (*marked)[currentVar] = result;
    return result;
}

void minimizeLearntClause(Context* ctx, vector<Lit>* learntClauseLits) {
    // Literal marking (mark all those existing in learnt clause except 1UIP)
    vector<bool> marked(ctx->numVars + 1, false), visited(ctx->numVars + 1, false);
    // For each marked literal X, if all "antecedents" (literals in reason clauses) are marked at some point,
    // then X can be removed from clause as it can be "inferred" by others (i.e. clause minimized)
    int j = learntClauseLits->size();
    for (int i = 0; i < j; i++) {
        Lit learntVar = LIT_VAR((*learntClauseLits)[i]);
        // Note: must at least check for reason clause of learntVar, regardless visited in previous iterations or not
        visited[learntVar] = false;
        marked[learntVar] = true;
        // If literal can be inferred, can be removed (move another literal from the back to replace it)
        if (isMarked(ctx, learntVar, learntVar, &marked, &visited))
            (*learntClauseLits)[i--] = (*learntClauseLits)[--j];
        marked[learntVar] = true;
    }
    // Remove all unnecessary literals (only first j are relevant)
    learntClauseLits->resize(j);
}


// ------------------------------ 5 DECISION MAKING/UNDOING ------------------------------

void makeDecision(Context* ctx, Lit lit, unsigned reasonClauseIndex) {
    unsigned var = LIT_VAR(lit);
    ctx->decMap[var] = (Decision){ lit, ctx->decLevel, ctx->numDecisions, reasonClauseIndex };
    ctx->decTrail[ctx->numDecisions++] = lit;
    // LRB statistic update (new direct assignment, not used in reasoning/conflict yet)
    ctx->lrb.varStats[var].assigned = ctx->lrb.learntCounter;
    ctx->lrb.varStats[var].participatedOrReasoned = 0; 
}

void undoDecision(Context* ctx) {
    if (ctx->numDecisions <= 0) return;
    unsigned var = LIT_VAR(ctx->decTrail[--ctx->numDecisions]);
    ctx->decMap[var] = INVALID_DECISION;
    // LRB statistic update
    LRBVarStats* varStat = &ctx->lrb.varStats[var];
    unsigned interval = ctx->lrb.learntCounter - varStat->assigned;
    if (interval <= 0) return;
    varStat->value = ((1.0 - ctx->lrb.alpha) * varStat->value) +
        (ctx->lrb.alpha * (double)(varStat->participatedOrReasoned) / (double)interval);
}

void makeHeuristicDecision(Context* ctx) {
    // Assign true/false value at random for initial decision
    unsigned varDecided = 0;
    // Branching based on LRB Statistics
    for (unsigned i = 1; i <= ctx->numVars; i++) {
        if (ctx->decMap[i].lit != INVALID_LIT) continue;
        // Decide on current literal if
        // 1) No variable is selected yet
        // 2) Current variable statistic is superior
        // 3) Current variable statistic is comparable (within 1e-6), random coin flip says use it instead
        // - Disable option 3 to eliminate randomness
        if (varDecided == 0 ||
            (ctx->lrb.varStats[varDecided].value < ctx->lrb.varStats[i].value) || 
            (ENABLE_RANDOM && ctx->lrb.varStats[varDecided].value - ctx->lrb.varStats[i].value <= 1e-6 && rand() % 2 == 1)) {
            varDecided = i;
        }
    }
    // Make a decision (true/false at random) at new decision level
    ++ctx->decLevel;
    makeDecision(ctx, LIT_MAKE(varDecided, TERNARY(ENABLE_RANDOM, rand() % 2, false)), INVALID_CLAUSE_INDEX);
}

// ------------------------------ 6 RESTART MECHANISM(S) ------------------------------

void initializeLRBStats(Context* ctx) {
    LRBStats* stats = &ctx->lrb;
    stats->alpha = LRB_ALPHA_INITIAL_VALUE;
    stats->learntCounter = 0;
    stats->varStats.clear();
    stats->varStats.reserve(ctx->numVars + 1);
    for (unsigned i = 0; i <= ctx->numVars; i++) {
        stats->varStats.push_back((LRBVarStats) { 0.0, 0, 0 });
    }
}

void clauseDeletion(Context* ctx) {
    // Ignore deletion if there is nothing to delete
    if (ctx->clauses.size() == ctx->numGivenClauses) return;
    if (DEBUG) cout << "c Clause Deletion: " << ctx->clauses.size();
    // Note: Level-0 reason clauses may be modified as a result (i.e. not preserved)
    //       However, result remains correct (level-0 items will not be changed/removed).
    unsigned j = ctx->clauses.size();
    for (int i = 0; i < j; i++) {
        // Sort literals for subsequent "includes" comparison
        sort(ctx->clauses[i].lits.begin(), ctx->clauses[i].lits.end());
        // Keep core clauses
        if (i < ctx->numCoreClauses) continue;
        // Only consider keeping any clause with LBD <= 4 (note: LBD = 2 is "glue" clause), and any clause causing level-0 unit prop.
        if (ctx->clauses[i].LBD > 4) {
            ctx->clauses[i--] = ctx->clauses[--j];
            continue;
        }
        // Check if clause can be subsumed by a clause to be kept. If so, don't need to keep
        bool isSubsumed = false;
        for (int k = i - 1; !isSubsumed && k >= 0; k--) {
            if (ctx->clauses[k].lits.size() > ctx->clauses[i].lits.size()) continue;
            isSubsumed = includes(ctx->clauses[i].lits.begin(), ctx->clauses[i].lits.end(), 
                                  ctx->clauses[k].lits.begin(), ctx->clauses[k].lits.end());
        }
        if (isSubsumed) ctx->clauses[i--] = ctx->clauses[--j];
    }
    // Eliminate all unused clauses
    ctx->clauses.resize(j);
    // Rebuild entire 2WL structure
    for (unsigned i = 0; i < ctx->litArraySize; i++) ctx->twoWL[i].clear();
    for (unsigned i = 0; i < ctx->clauses.size(); i++) {
        Clause* clause = &ctx->clauses[i];
        // Note: must restore original watch literals before rebuilding
        if (clause->WL[0] != INVALID_LIT) ctx->twoWL[clause->WL[0]].push_back(i);
        if (clause->WL[1] != INVALID_LIT) ctx->twoWL[clause->WL[1]].push_back(i);
    }
    // Update core clause count
    ctx->numCoreClauses = ctx->clauses.size();
    if (DEBUG) cout << " -> " << ctx->numCoreClauses << endl;
}

void restart(Context* ctx) {
    // Undo all decisions except decision level 0
    while (ctx->numDecisions > 0 && 
           ctx->decMap[LIT_VAR(ctx->decTrail[ctx->numDecisions - 1])].decLevel != 0) undoDecision(ctx);
    // Start from decision level 0, no conflicts, no statistics
    ctx->decLevel = 0;
    ctx->conflictsSinceRestart = 0;
    initializeLRBStats(ctx);
    // Reduce number of learnt
    clauseDeletion(ctx);
    // Compute next Luby restart values
    if (ctx->lubyRestart.first > ctx->lubyRestart.second) {
        ctx->lubyRestart.first = 1;
        ctx->lubyRestart.second <<= 1;
    } else {
        ctx->lubyRestart.first <<= 1;
    }
}

// ------------------------------ 7 CONFLICT RESOLUTION ------------------------------

// Assumes that all literals have an associated decision when calling this function
void findLastDecIndex(Context* ctx, vector<Lit>* lits, unsigned* lastDecIndex, unsigned* secondLastDecIndex) {
    *lastDecIndex = ctx->decMap[LIT_VAR((*lits)[0])].decTrailIndex;
    *secondLastDecIndex = INVALID_DEC_INDEX;
    for (unsigned i = 1; i < lits->size(); i++) {
        unsigned decIndex = ctx->decMap[LIT_VAR((*lits)[i])].decTrailIndex;
        if (decIndex > *lastDecIndex) {
            *secondLastDecIndex = *lastDecIndex;
            *lastDecIndex = decIndex;
        } else if (decIndex > *secondLastDecIndex || *secondLastDecIndex == INVALID_DEC_INDEX) {
            *secondLastDecIndex = decIndex;
        }
    }
}

void resolveConflict(Context* ctx, unsigned unsatClauseIndex) {
    // Placeholder for index to key decisions
    unsigned lastDecIndex = INVALID_DEC_INDEX, secondLastDecIndex = INVALID_DEC_INDEX;
    // Construct learnt clause (incl. placeholder values)
    // - LBD starts from 1 (representing current decision level)
    ctx->clauses.push_back((Clause) {});
    Clause* learntClause = &(ctx->clauses[ctx->clauses.size() - 1]);
    learntClause->LBD = 1;
    learntClause->WL[0] = INVALID_LIT;
    learntClause->WL[1] = INVALID_LIT;
    learntClause->lastSATLit = INVALID_LIT;
    // Found a conflict
    ++ctx->conflictsSinceRestart;
    Clause* unsatClause = &ctx->clauses[unsatClauseIndex];
    findLastDecIndex(ctx, &unsatClause->lits, &lastDecIndex, &secondLastDecIndex);
    while (lastDecIndex + 1 < ctx->numDecisions) undoDecision(ctx);
    // Track variables seen, decision levels seen
    vector<bool> varSeen(ctx->numVars + 1, false), decLevelSeen(ctx->numVars + 1, false);
    // Count for the number of unprocessed but seen variables from current decision level, unitialized to 0
    unsigned count = 0;
    // Process in reverse-chronological order of decisions
    unsigned lastDecisionVar = LIT_VAR(ctx->decTrail[ctx->numDecisions - 1]);
    unsigned lastDecLevel = ctx->decMap[lastDecisionVar].decLevel;
    decLevelSeen[lastDecLevel] = true;
    // Find 1UIP procedure (https://efforeffort.wordpress.com/2009/03/09/linear-time-first-uip-calculation/)
    Clause* reasonClause; 
    bool firstClause = true;
    do {
        // Start from UNSAT clause
        if (firstClause) reasonClause = unsatClause;
        else {
            unsigned reasonClauseIndex = ctx->decMap[lastDecisionVar].reasonClauseIndex;
            // Reached a decision made by heuristics alone, no more reasoning, stop
            if (reasonClauseIndex == INVALID_CLAUSE_INDEX) break;
            else reasonClause = &ctx->clauses[reasonClauseIndex];
        }
        // Process literals of reasonClause
        for (unsigned i = 0; i < reasonClause->lits.size(); i++) {
            // For each literal causing the unit propagation to lastDecision
            unsigned reasonClauseVar = LIT_VAR(reasonClause->lits[i]);
            // Ignore seen literals
            if (varSeen[reasonClauseVar]) continue;
            varSeen[reasonClauseVar] = true;
            // If reason literal is from current decision level, increment count (seen but unprocessed)
            // Note: reason clause should not have any literals whose variables are undecided
            Decision reasonClauseLitDecision = ctx->decMap[reasonClauseVar];
            if (reasonClauseLitDecision.decLevel == lastDecLevel) {
                count++;
                continue;
            }
            // Otherwise, it is part of learnt clause (from another decision level) - NEGATE IT!
            learntClause->lits.push_back(LIT_NEG(reasonClauseLitDecision.lit));
            // Update LBD statistic for learnt clause
            if (reasonClauseLitDecision.lit != INVALID_LIT &&
                !decLevelSeen[reasonClauseLitDecision.decLevel]) {
                decLevelSeen[reasonClauseLitDecision.decLevel] = true;
                ++learntClause->LBD;
            }
        }

        do {
            if (firstClause) break;
            // Undo decision
            undoDecision(ctx);
            // Look for next candidate for 1UIP
            lastDecisionVar = LIT_VAR(ctx->decTrail[ctx->numDecisions - 1]);
        } while(!varSeen[lastDecisionVar]);
        firstClause = false;
        count--;
    } while (count > 0);
    // Clause minimization for anything that is not 1UIP
    minimizeLearntClause(ctx, &learntClause->lits);
    // Add 1UIP to learnt clause (negation of decision), set it as watch literal of learnt clause
    Lit oneUIPLit = LIT_NEG(ctx->decMap[lastDecisionVar].lit);
    learntClause->lits.push_back(oneUIPLit);
    ctx->twoWL[oneUIPLit].push_back(ctx->clauses.size() - 1);
    learntClause->WL[0] = oneUIPLit;
    
    // Idea: Locate 2nd last decision for potential backtracking to
    findLastDecIndex(ctx, &learntClause->lits, &lastDecIndex, &secondLastDecIndex);

    // For backtracking to unit clause, backtrack to decision level 0, then add unit clause
    if (secondLastDecIndex == INVALID_DEC_INDEX) {
        // Backtrack to last unit clause (if any) at decision level 0
        ctx->decLevel = 0;
        while (ctx->numDecisions > 0 && ctx->decMap[LIT_VAR(ctx->decTrail[ctx->numDecisions - 1])].decLevel != 0) undoDecision(ctx);
        // Previously assigned unit clause for same variable but different truth values = UNSAT
        Decision dec = ctx->decMap[LIT_VAR(learntClause->lits[0])];
        ctx->isSAT = (dec.lit == INVALID_LIT) || (dec.lit == learntClause->lits[0]);
        // Make the decision for this unit clause for displaying UNSAT if need be
        makeDecision(ctx, learntClause->lits[0], INVALID_CLAUSE_INDEX);
        // Progress tracking purposes (esp. UNSAT instances)
        cout << "c Unit clause ("; displayLit(learntClause->lits[0]);
        cout << ") generated from conflict. Count: " << (++ctx->numGeneratedUnitClauses) << endl;
    // Otherwise, for non-unit clauses, backtrack till 2nd last decision (for subsequent unit propagation from there)
    } else {
        // Undo all decisions until 2nd last decision in learnt clause
        while (ctx->numDecisions > 0 && secondLastDecIndex + 1 < ctx->numDecisions) undoDecision(ctx);
        // Add learnt clause to 2WL for unit propagation
        unsigned lastDecLitNeg = LIT_NEG(ctx->decTrail[ctx->numDecisions - 1]);
        ctx->twoWL[lastDecLitNeg].push_back(ctx->clauses.size() - 1);    
        learntClause->WL[1] = lastDecLitNeg;
        // In the end, allow for unit propagation from the right decision level
        ctx->decLevel = ctx->decMap[LIT_VAR(ctx->decTrail[ctx->numDecisions - 1])].decLevel;
    }
}

void afterConflictAnalysis(Context* ctx, unsigned unsatClauseIndex) {
    Clause* unsatClause = &ctx->clauses[unsatClauseIndex];
    Clause* learntClause = &ctx->clauses.back();
    // LRB Statistic update
    // Learnt a clause
    ++ctx->lrb.learntCounter;
    // Every literal in learnt clause and UNSAT clause participated
    vector<bool> seen(ctx->numVars, false);
    // Update literals that participated in conflict
    for (unsigned i = 0; i < unsatClause->lits.size(); i++) {
        unsigned var = LIT_VAR(unsatClause->lits[i]);
        if (seen[var]) continue;
        seen[var] = true;
        ++ctx->lrb.varStats[var].participatedOrReasoned;
    }
    for (unsigned i = 0; i < learntClause->lits.size(); i++) {
        unsigned var = LIT_VAR(learntClause->lits[i]);
        if (seen[var]) continue;
        seen[var] = true;
        ++ctx->lrb.varStats[var].participatedOrReasoned;
    }
    // Slow down rate of learning
    if (ctx->lrb.alpha > LRB_ALPHA_MIN) ctx->lrb.alpha -= LRB_ALPHA_DECAY;
    // RSR extension (less "need" to apply on unit clauses learnt): 
    for (unsigned i = 0; i < learntClause->lits.size() - 1; i++) {
        // If already decided, look for clause that caused it (reason literals) and +1 reasoned for them
        // 1UIP literal will be due to the other learnt clause literals...
        Lit non1UIPLit = learntClause->lits[i];
        ++ctx->lrb.varStats[LIT_VAR(non1UIPLit)].participatedOrReasoned;
        if (ctx->decMap[LIT_VAR(non1UIPLit)].lit == INVALID_LIT ||
            ctx->decMap[LIT_VAR(non1UIPLit)].reasonClauseIndex == INVALID_CLAUSE_INDEX) continue;
        // Found a reason clause for the learnt clause literals, include in computation
        Clause* reasonClause = &ctx->clauses[ctx->decMap[LIT_VAR(non1UIPLit)].reasonClauseIndex];
        for (unsigned j = 0; j < reasonClause->lits.size(); j++) {
            ++ctx->lrb.varStats[LIT_VAR(reasonClause->lits[j])].participatedOrReasoned;    
        }
    }
    // Locality extension: For every unassigned variable, decay the LRB statistic value
    for (unsigned i = 1; i <= ctx->numVars; i++) {
        if (ctx->decMap[i].lit != INVALID_LIT) continue;
        ctx->lrb.varStats[i].value *= LRB_DECAY_RATE;
    }
}

// ------------------------------ 8 UNIT PROPAGATION ------------------------------

// Note: Bottleneck method
unsigned checkClause(Context* ctx, Clause* clause) {
    // If clause was previously satisfied by something that is still "decided", no need process
    if (clause->lastSATLit != INVALID_LIT && 
        ctx->decMap[LIT_VAR(clause->lastSATLit)].lit != INVALID_LIT &&
        ctx->decMap[LIT_VAR(clause->lastSATLit)].lit == clause->lastSATLit) {
        return CLAUSE_SATISFIED;
    }
    clause->lastSATLit = INVALID_LIT;
    // Note: Search for some unassigned variable (for unit prop. and watch) at the same time
    ctx->tempLit = INVALID_LIT;
    Lit clauseLit;
    // Otherwise, enumerate all literals in the clause...
    for (unsigned i = 0, numLits = clause->lits.size(); i < numLits; i++) {
        clauseLit = clause->lits[i];
        Decision dec = ctx->decMap[LIT_VAR(clauseLit)];
        // variable is assigned -> (1) assigned true and not negated, (2) assigned false and negated
        if (dec.lit == clause->lits[i]) {
            clause->lastSATLit = clauseLit;
            return CLAUSE_SATISFIED;
        }
        // Unassigned variable remaining, check if it can become a new watch literal (i.e. not currently one)
        if (dec.lit == INVALID_LIT) {
            ctx->tempLit = clauseLit;
            // Optimization: more than 1 unassigned literal = unknown/SAT -> stop checking immediately + mark new WL
            if(clause->WL[0] != clauseLit && clause->WL[1] != clauseLit) return CLAUSE_UNKNOWN;
        }
    }
    if (ctx->tempLit != INVALID_LIT) return CLAUSE_UNKNOWN_UNIT;
    return CLAUSE_UNSATISFIED;
}

// Note: Bottleneck method
unsigned doUnitPropagation(Context* ctx) {
    // No decisions = nothing to propagate
    if (ctx->numDecisions == 0) return INVALID_CLAUSE_INDEX;
    // Propagate from last decision made
    unsigned queueStart = ctx->numDecisions - 1;// Note: queueEnd = ctx->numDecisions;
    while (queueStart < ctx->numDecisions) {
        // Obtain negation of literal for unit propagation (was set to false)
        Lit upLitNeg = LIT_NEG(ctx->decTrail[queueStart++]);
        // Use 2WL (2 Watched Literal) structure to locate relevant clauses
        // Look for clauses where literal became "false"
        vector<unsigned>* upWatchList = &ctx->twoWL[upLitNeg];
        int j = upWatchList->size();
        for (int i = 0; i < j; i++) {
            // Process current clause
            unsigned clauseIndex = (*upWatchList)[i];
            Clause* clause = &ctx->clauses[clauseIndex];
            unsigned result = checkClause(ctx, clause);
            // If they are no longer satisfied, found conflict and stop unit propagation
            if (result == CLAUSE_UNSATISFIED) {
                // Remove invalid entries
                upWatchList->resize(j);
                return clauseIndex;
            }
            // If clause is already satisfied, look for next clause
            else if (result == CLAUSE_SATISFIED) continue;
            // If clause is still unknown with 1 unassigned variable, satisfy the clause using it and unit propagate
            else if (result == CLAUSE_UNKNOWN_UNIT) {
                // Unit propagate normally (make the new decision)
                makeDecision(ctx, ctx->tempLit, clauseIndex);
            // Otherwise, use another unassigned literal in clause as new WL, if available
            } else if (result == CLAUSE_UNKNOWN && ctx->tempLit != INVALID_LIT) {
                // Move another clause index to current position instead
                (*upWatchList)[i--] = (*upWatchList)[--j];
                // Found new WL to use, add clause to new WL's watchlist instead            
                ctx->twoWL[ctx->tempLit].push_back(clauseIndex);
                if (clause->WL[0] == upLitNeg) clause->WL[0] = ctx->tempLit;
                if (clause->WL[1] == upLitNeg) clause->WL[1] = ctx->tempLit;
            }
        }
        // Remove invalid entries
        upWatchList->resize(j);
    }
    // No UNAT clauses
    return INVALID_CLAUSE_INDEX;
}

// ------------------------------ 9 PRE-PROCESSING ------------------------------

void preprocessClauses(Context* ctx) {
    // Store potential pure literals (only positive or negation of variable exists)
    vector<bool> positive(ctx->numVars + 1, false), negative(ctx->numVars + 1, false);
    // Look for unit clauses
    for (unsigned i = 0; ctx->isSAT && i < ctx->clauses.size(); i++) {
        Clause* clause = &ctx->clauses[i];
        // If it is a unit clause
        if (clause->lits.size() == 1) {
            Decision dec = ctx->decMap[LIT_VAR(clause->lits[0])];
            // If different true/false values assigned for same variable, UNSAT
            ctx->isSAT = dec.lit == INVALID_LIT || dec.lit == clause->lits[0];
            makeDecision(ctx, clause->lits[0], INVALID_CLAUSE_INDEX);
            cout << "c Identified unit clause: ("; displayLit(clause->lits[0]); cout << ")" << endl;
        }
        // Track sign of each literal in the clause
        for (unsigned j = 0; j < clause->lits.size(); j++) {
            if (LIT_SIGN(clause->lits[j])) positive[LIT_VAR(clause->lits[j])] = true;
            else negative[LIT_VAR(clause->lits[j])] = true;
        }
    }
    // Look for pure literals
    for (unsigned i = 1; ctx->isSAT && i <= ctx->numVars; i++) {
        if (positive[i] == negative[i]) continue;
        // Found a pure literal, attempt to assign a value not already done (e.g. by unit clause)
        cout << "c Identified pure literal: " << TERNARY(positive[i], "", "-") << i << endl;
        Decision dec = ctx->decMap[i];
        if (dec.lit == INVALID_LIT) {
            makeDecision(ctx, LIT_MAKE(i, positive[i]), INVALID_CLAUSE_INDEX);    
        // Pure literal conflicts with previous unit clause decision, UNSAT
        } else if (LIT_SIGN(dec.lit) != positive[i]) {
            ctx->isSAT = false;
        }
    }
    // If any clause is UNSAT at this point, formula is UNSAT (pure literals and unit clauses used only)
    for (unsigned i = 0; ctx->isSAT && i < ctx->numGivenClauses; i++)
        if (checkClause(ctx, &ctx->clauses[i]) == CLAUSE_UNSATISFIED)
            ctx->isSAT = false;
}

// ------------------------------ 10 SAT SOLVER MAIN LOGIC ------------------------------

void solve(Context* ctx) {
    // Restart on clean slate before starting to solve
    restart(ctx);
    // Pre-process clauses
    preprocessClauses(ctx);
    // Begin CDCL Algorithm
    while (ctx->isSAT) {
        // Perform unit propagation
        unsigned unsatClauseIndex = doUnitPropagation(ctx);
        // Conflict found, process it
        if (unsatClauseIndex != INVALID_CLAUSE_INDEX) {
            // Conflict at decision level 0 = conflict with unit clause = UNSAT
            if (ctx->decLevel == 0) ctx->isSAT = false;
            resolveConflict(ctx, unsatClauseIndex);
            if (!ctx->isSAT) break;
            afterConflictAnalysis(ctx, unsatClauseIndex);
            // Restart if required (e.g. 256 * lubyRestart Multiplier)
            if(ctx->conflictsSinceRestart > (ctx->lubyRestart.first << 6)) restart(ctx);
        // No conflict found, attempt to assign new variable
        } else if (ctx->numDecisions < ctx->numVars) {
            makeHeuristicDecision(ctx);
        // Done
        } else break;
    }
    // Double check for errors against only original clauses (esp. if solution is SAT)
    for (unsigned i = 0; ctx->isSAT && i < ctx->numGivenClauses; i++) {
        if (checkClause(ctx, &ctx->clauses[i]) != CLAUSE_SATISFIED) {
            cout << "c [!] SAT Solver Error: Found solution does not satisfy all given clauses." << endl;
            return;
        }
    }
    // No errors, write solution in DIMACS output format
    writeDimacs(ctx);
}

// ------------------------------ 11 PROGRAM MAIN LOGIC ------------------------------

int main(int argc, char** argv) {
    // Speed up C++ I/O if possible
    ios_base::sync_with_stdio(false);
    cin.tie(NULL);
    cout.tie(NULL);
    // Random seed
    srand(time(NULL));
    // Read from file (DIMACS CNF format)
    Context ctx;
    if (argc < 2 || !readDimacs(argv[1], &ctx)) return -1;
    solve(&ctx);
    // Done
    return 0;
}
