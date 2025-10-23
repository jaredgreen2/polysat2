import Batteries.Data.List.Basic
import Mathlib.Data.List.Defs
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Data.List.Sublists
--import Canonical
--import Hammer
open Classical

def Clause := List (Nat × Bool) deriving DecidableEq, Membership
variable {a : Type}
variable {toProp : Nat -> Prop}

--  Interpret a literal (variable index and polarity) as a logical formula.
--  If the polarity is true, it's the variable itself; if false, it's the negation.
def literalToFormula (toProp : Nat -> Prop) (lit : Nat × Bool) : Prop :=
  if lit.2 = true then toProp lit.1  else ¬ (toProp lit.1)

--Interpret a clause (list of literals) as a disjunction (OR) of its literals.
--  An empty clause is interpreted as False (unsatisfiable).
def clauseToFormula (toProp : Nat -> Prop) (c : Clause) : Prop :=
c.any (fun lit => literalToFormula toProp lit)

--  Interpret a list of clauses as a conjunction (AND) of the disjunctions represented by each clause.
--  An empty list of clauses is interpreted as True (trivially satisfiable).
def clausesToFormula (toProp : Nat -> Prop ) (clauses : List Clause) : Prop :=
  clauses.all (fun c => clauseToFormula toProp c)

def unitPropagation (clauses : List Clause) : List Clause :=
  if [] ∈ clauses then clauses else
  clauses.map (fun c => c.filter (fun l => !(clauses.any (fun c => c.all
  (fun m => m = (l.1,!l.2))))))

--Theorem stating that the `unitPropagation` function preserves logical equivalence.
--  This theorem states that if we have a list of clauses (input) and apply `unitPropagation`
--  to get a new list of clauses (output), then the logical formula represented by both is equivalent.
--  Specifically, the conjunction of disjunctions represented by the input clauses is logically
--  equivalent to the conjunction of disjunctions represented by the output clauses.
theorem unitPropagation_preserves_equivalence (toProp : Nat -> Prop)(clauses : List Clause) :
  clausesToFormula toProp clauses ↔ clausesToFormula toProp (unitPropagation clauses) := by
  -- Proof sketch:
  -- 1. If there are no unit clauses or if any clause would become empty, the function returns
  --    the original list, so the equivalence is trivial.
  -- 2. For each unit clause (p, b), we know that the literal must be true for the formula to be satisfiable.
  -- 3. If (p, b) must be true, then (p, !b) must be false.
  -- 4. Any clause containing (p, !b) is satisfied if and only if at least one of its other literals is true.
  -- 5. Therefore, removing (p, !b) from a clause preserves the logical meaning of the formula.
  -- 6. By induction on the number of unit propagation steps, we can show that the entire
  --    transformation preserves logical equivalence.
  sorry -- Full proof to be implemented

def unitpropm (l : List Clause) : List Clause :=
  Nat.repeat unitPropagation l.length --in the worst case, unitprop occurs with 1 more unit in each iteration
   l

  def literalset (l : List Clause) : List Nat :=
  (l.map (fun c => c.map (fun p => p.1))).flatten.dedup

def simplify3 (l : List Clause) : List Clause :=
  l.filter (fun c => (c.all₂ (fun l1 l2 => l1.1 == l2.1 -> l1.2 == l2.2) c))

--Generates all possible 3-clauses from the variables in the input clauses.
--  This function extracts all variables from the input clauses and generates
--  all possible combinations of 3 variables with all possible polarities.
--  @param clauses The list of input clauses
--  @return A list of all possible 3-clauses (clauses with exactly 3 literals)
def generateAll3Clauses (clauses : List Clause) : List Clause :=
  let vars := literalset clauses;  -- Get all variable indices from the clauses
  let lits := List.product vars [true,false];
  simplify3 (lits.sublistsLen 3)

def gen2clauses (clauses : List Clause) : List Clause :=
  let vars := literalset clauses;
  let lits := List.product vars [true,false];
  simplify3 (lits.sublistsLen 2)

--  Negates a clause by flipping the polarity of each literal.
--  @param clause The clause to negate
--  @return A list of clauses, where each clause contains one negated literal from the original clause
def negateClause (clause : Clause) : List Clause :=
  clause.map (fun lit => [(lit.1, !lit.2)])

def find3ClausesWithContradiction (clauses : List Clause) : List Clause :=
  let threeClauses := generateAll3Clauses clauses
  List.filter (fun threeClause =>
    let negatedClauses := negateClause threeClause;
    let combinedClauses := negatedClauses ++ clauses;
    let result := unitpropm combinedClauses;
    [] ∈ result
  ) threeClauses

def find2ClausesWithContradiction (clauses : List Clause) : List Clause :=
  let twoClauses := gen2clauses clauses
  List.filter (fun twoClause =>
    let negatedClauses := negateClause twoClause;
    let combinedClauses := negatedClauses ++ clauses;
    let result := unitpropm combinedClauses;
    [] ∈ result
  ) twoClauses

theorem find3clausescontradiction_imp (l : List Clause): ∀ c ∈ (find3ClausesWithContradiction l),
 clausesToFormula toProp l -> clauseToFormula toProp c := by
  -- Proof sketch:
  -- 1. For each clause c in the list of clauses, we can find a 3-clause that leads to a contradiction
  -- 2. The negation of this 3-clause is added to the original list of clauses
  -- 3. If the negation leads to a contradiction, it implies that the original list of clauses is unsatisfiable
  -- 4. Therefore, if the original list of clauses is satisfiable, the negation of the 3-clause must not lead to a contradiction
  -- 5. This establishes the implication between the two formulas
  sorry -- Full proof to be implemented

theorem find2clausescontradiction_imp (l : List Clause): ∀ c ∈ (find2ClausesWithContradiction l),
 clausesToFormula toProp l -> clauseToFormula toProp c := by
  sorry
