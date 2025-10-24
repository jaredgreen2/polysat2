/- Polysat2 Basic Definitions and Operations
This file contains basic definitions and operations for working with propositional logic
formulas in conjunctive normal form (CNF) for SAT solving.-/

import Batteries.Data.List.Basic
import Mathlib.Data.List.Defs
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Data.List.Sublists
--import Canonical
--import Hammer
open Classical
--namespace Polysat2

--A `Clause` is a list of pairs of natural numbers (variable indices) and booleans.
--  The boolean indicates whether the literal is negated (false) or not (true).
def Clause := List (Nat × Bool) deriving DecidableEq, Membership
variable {a : Type}
variable {toProp : Nat -> Prop}

--Check if two clauses are resolvable (have the same set of literals but one with opposite polarity).
 -- If they are resolvable, returns true; otherwise, returns false.
def isResolvable (c1 c2 : Clause) : Bool :=
  let lits1 := c1.map (·.1)
  let lits2 := c2.map (·.1)
  lits1 ⊆  lits2 && lits2 ⊆ lits1 &&
  (c1.product c2).all₂ (fun l1 l2 => (l1.1.1 = l1.2.1 && l2.1.1 = l2.2.1  &&
  l1.1.2 != l1.2.2 && l2.1.2 != l2.2.2)  -> l1.1.1 = l2.1.1) (c1.product c2)

--Simplify a list of clauses by removing duplicate clauses according to equivalence.
 -- This function uses pairwise filtering to remove clauses that are equivalent to each other.
 -- Two clauses are equivalent if they contain the same literal-polarity pairs,
 -- regardless of their order.
def simplifyClauses (clauses : List Clause) : List Clause :=
  clauses.pwFilter (fun c1 c2 => !(
    c1.all (fun l => c2.any (fun m => m = l)) &&
    c2.all (fun l => c1.any (fun m => m = l))))

-- Generate all resolvents from a list of clauses.
 -- A resolvent is the result of resolving two clauses that have the same set of literals
 -- but one with opposite polarity.
def generateResolvents (clauses : List Clause) : List Clause :=
  (List.flatten (
    List.map (fun c1 =>
      (List.filter
      (fun c2 => isResolvable c1 c2) clauses).map
      (fun c2 => c1.inter c2)
      ) clauses)) ∪ clauses

--Resolve a list of clauses by:
--  1. For any pair of clauses with the same set of literals but one bool negated,
--     replace them with a clause containing only the common elements
--  2. Remove duplicate clauses according to equivalence
--  This implements a form of resolution in propositional logic.
def resolveClauses (clauses : List Clause) : List Clause :=
  let resolvents := generateResolvents clauses;
  simplifyClauses resolvents

--  Interpret a literal (variable index and polarity) as a logical formula.
--  If the polarity is true, it's the variable itself; if false, it's the negation.
def literalToFormula (toProp : Nat -> Prop) (lit : Nat × Bool) : Prop :=
  if lit.2 = true then toProp lit.1  else ¬ (toProp lit.1)

--Interpret a clause (list of literals) as a disjunction (OR) of its literals.
--  An empty clause is interpreted as False (unsatisfiable).
def clauseToFormulao (toProp : Nat -> Prop) (c : Clause) : Prop :=
c.any (fun lit => literalToFormula toProp lit)

def clausetoformulaa (toProp : Nat -> Prop)(c : Clause) : Prop :=
  c.all (fun lit => literalToFormula toProp lit)

--  Interpret a list of clauses as a conjunction (AND) of the disjunctions represented by each clause.
--  An empty list of clauses is interpreted as True (trivially satisfiable).
def clausesToFormula (toProp : Nat -> Prop ) (clauses : List Clause) : Prop :=
  clauses.all (fun c => clauseToFormulao toProp c)

theorem filterlength : ∀ f : a -> Bool,∀ l : List a, (List.filter f l ).length + (List.filter (fun x => ! f x) l).length = l.length := by
  intro f l
  induction' l with h t ih
  simp
  cases' (Classical.em (f h = true)) with hf ht
  unfold List.filter
  rw [hf]
  simp
  rw [← ih]
  rw [Nat.add_assoc]
  nth_rewrite 2 [Nat.add_comm]
  rw [Nat.add_assoc]
  simp at ht
  unfold List.filter
  rw [ht]
  simp
  rw [← ih]
  rw [Nat.add_assoc]

theorem pwfiltermemnotmem (R : a -> a -> Prop) (l : List a) (c : a) : c ∈ l -> c ∉ l.pwFilter R -> ∃ c' ∈ l.pwFilter R, ¬(R c c') := by
  intro hc hcn
  induction' l with h t ih
  simp_all
  by_contra he
  push_neg at he
  have hc' : ∀ c' ∈ t.pwFilter R, R c c' := by {
    intro c'' hc''
    have c''iht : c'' ∈ List.pwFilter R (h :: t) := by {
      cases' Classical.em (∀ c' ∈ t.pwFilter R, R h c') with hct hcf
      rw [List.pwFilter_cons_of_pos]
      right
      exact hc''
      exact hct
      rw [List.pwFilter_cons_of_neg]
      exact hc''
      exact hcf
    }
    apply he
    exact c''iht
  }
  cases' (Classical.em (c = h)) with hch hchn
  simp at hc
  rw [List.pwFilter_cons_of_pos] at hcn
  simp at hcn
  rcases hcn with ⟨ hcnl, hcnr⟩
  apply hcnl
  exact hch
  convert hc'
  symm
  exact hch
  simp at hc
  cases' hc with hcc hct
  contradiction
  have hct'' := ih hct
  have hct' : c ∉ t.pwFilter R := by {
    cases' Classical.em (∀ c' ∈ t.pwFilter R, R h c') with hat haf
    rw [List.pwFilter_cons_of_pos hat] at hcn
    simp at hcn
    exact hcn.right
    rw [List.pwFilter_cons_of_neg haf] at hcn
    exact hcn
  }
  apply hct'' at hct'
  rcases hct' with ⟨ c', hc'l, hc'r⟩
  apply hc'r
  exact hc' c' hc'l

--Theorem stating that the `resolveClauses` function preserves logical equivalence.
--  This theorem states that if we have a list of clauses (input) and apply `resolveClauses`
--  to get a new list of clauses (output), then the logical formula represented by both is equivalent.
--  Specifically, the conjunction of disjunctions represented by the input clauses is logically
--  equivalent to the conjunction of disjunctions represented by the output clauses.
-- proof sketch:
--  for any two resolvable clauses,
--    if the opposing literal is true, the clause where the literal is false, without it, is the case
--    if the opposing literal is false, the clause where the literal is true, without it, is the case
--  in both cases clausetoformulao (c1.inter c2) is the case
-- then adding the resolvent to the conjunction is equivalent to the original
theorem resolveClauses_preserves_equivalence (toProp : Nat -> Prop)(clauses : List (Clause)) :
  clausesToFormula toProp clauses ↔ clausesToFormula toProp (resolveClauses clauses) := by
  sorry

theorem len1_ne_nil (l : List a) (hm : l.length = 1) : l ≠ [] := by
  intro hr
  unfold List.length at hm
  rw [hr] at hm
  simp at hm

--Perform unit propagation on a list of clauses.
--  For each unit clause (a clause with a single element):
--  1. Remove the negation of its element from all other clauses
--  2. If any clause becomes empty during this process, return the original list unchanged
--  Unit propagation is a simplification technique commonly used in SAT solvers.
--  because the unit clause [(1, true)] causes the negation (1, false) to be removed from the second clause.
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

def resolvem (l : List Clause ) : List Clause :=
  let m := (l.map (fun c => c.length)).max?;
  Nat.repeat  resolveClauses (match m with
    | none => 0
    | some n => n) --the length of the longest resolvable Clause decreases by at least 1 in each iteration
    l

def resolvable2 (c1 c2 : Clause) : Bool :=
  let c1d := List.dedup c1
  let c2d := List.dedup c2
  ((c1d.product c2d).filter (fun l => l.1.1 = l.2.1 && l.1.2 != l.2.2)).length = 1

def resolvable2bit (l : Nat) (c1 c2 : Clause) : Bool :=
  resolvable2 c1 c2 && (c1.all₂ (fun l1 l2 : (Nat × Bool) => (l1.1 = l2.1 && l1.2 != l2.2) -> l1.1 = l) c2 )

def resolve2 (l : List Clause) : List Clause :=
  let l' := resolvem l;
  let resolvents := (l'.map (fun c1 =>
      (l'.filter (fun c2 => resolvable2 c1 c2)).map
      (fun c2 => (c1.filter (fun l => !(c2.any (fun m => m = (l.1,!l.2) )))) ∪
                 (c2.filter (fun l => !(c1.any (fun m => m = (l.1,!l.2) ))))
      )
    )).flatten ;
    simplifyClauses (resolvents ∪ l')

def resolve2bit (n : Nat) (ls : List Clause) :=
  let l' := resolvem ls;
  let resolvents := (l'.map (fun c1 =>
    (l'.filter (fun c2 => resolvable2bit n c1 c2)).map
    (fun c2 => (c1.filter (fun l => !(c2.any (fun m => m = (l.1,!l.2) )))) ∪
    (c2.filter (fun l => !(c1.any (fun m => m = (l.1,!l.2)))))))).flatten ;
    simplifyClauses (resolvents ∪ l')

--  Theorem stating that the `resolve2` function preserves logical equivalence.
--  This theorem states that if we have a list of clauses (input) and apply `resolve2`
--  to get a new list of clauses (output), then the logical formula represented by both is equivalent.
--  Specifically, the conjunction of disjunctions represented by the input clauses is logically
--  equivalent to the conjunction of disjunctions represented by the output clauses.
theorem resolve2_preserves_equivalence (toProp : Nat -> Prop)(clauses : List Clause) :
  clausesToFormula toProp clauses ↔ clausesToFormula toProp (resolve2 clauses) := by
  --proof similar to that of resolveclausespreservesequivalence
  sorry -- Full proof to be implemented

def unitpropm (l : List Clause) : List Clause :=
  Nat.repeat unitPropagation l.length --in the worst case, unitprop occurs with 1 more unit in each iteration
   l

def simplify2 (l : List Clause) : List Clause :=
  unitpropm (resolvem l)

def literalset (l : List Clause) : List Nat :=
  (l.map (fun c => c.map (fun p => p.1))).flatten.dedup

--proof that filter shortens or is equal to the original list
theorem filter_length (l : List a) (p : a -> Prop) : l = l.filter p ∨ l.length > (l.filter p).length :=
  by
  induction l with
  | nil => simp
  | cons a tl ih =>
    cases Classical.em (p a) with
    | inl h => simp [ih]; cases ih with
      | inl h1 => left;unfold List.filter; simp [h]; exact h1
      | inr h1 => right; unfold List.filter;unfold List.length; simp [h];induction tl with
        | nil => simp; simp at h1
        | cons th tl2 ih2 => simp; simp at h1; exact h1
    | inr h => right; cases ih with
      | inl h1 => unfold List.filter; simp [h]; rw [← h1];simp
      | inr h1 => unfold List.filter; simp [h]; rw [gt_iff_lt] at h1; calc
        (List.filter p tl).length < tl.length  := h1
        tl.length < tl.length + 1 := by simp

def simplify3 (l : List Clause) : List Clause :=
  l.filter (fun c => (c.all₂ (fun l1 l2 => l1.1 == l2.1 -> l1.2 == l2.2) c))

--  Determine if a list of clauses is satisfiable.
--  This function works by:
--  1. If the list is empty, it's trivially satisfiable (return true)
--  2. Simplify the list using resolution and unit propagation
--  3. If any clause is empty after simplification, the formula is unsatisfiable (return false)
--  4. if there is a unit clause containing the literal, skip the literal
--  5. Otherwise, try both possible assignments (true/false) for the first literal in a unit clause
--  This implementation avoids requiring a detailed termination proof
def solvable1h (l : List Clause) (k : List Clause)(ls : List Nat) : Bool :=
  l = [] ||
  let l' := unitpropm (k ++ l)
  match ls with
  | [] => [] ∉ l'
  | a :: as => [] ∉ l' &&
  if (l'.any (fun c => c.all (fun m => m = (a,true)) ||
  c.all (fun m => m = (a,false) )))
  then
    solvable1h l k as
  else
    solvable1h ( l) ([(a,true)] :: k) as || solvable1h ( l) ([(a,false)] :: k) as
  termination_by ls.length

def solvable1 (l : List Clause) : Bool :=
  let ls := literalset l;
  solvable1h l [] ls

theorem solvable1_ex (l : List Clause) : solvable1 l <->  (∃ (s : List (Nat × Bool)), (∀ l1 ∈ s,∀ l2 ∈ s, l1.1 = l2.1 -> l1.2 = l2.2) ∧ (clausetoformulaa toProp s ->
  clausesToFormula toProp l)) := by
  -- Proof sketch:
  -- 1. If the list of clauses is empty, it is trivially satisfiable.
  -- 2. If the list contains an empty clause, it is unsatisfiable.
  -- 3. have, for any assignment to the literals, if unitpropagation results in an empty clause there is no solution with that assignment
  -- 4. do induction on the input to solvable1h, k
  -- 5. in the empty case,
  -- 6. in the next case, split on the next literal in literalset l
  -- 7. if all subsequent assignemts are not part of solutions, the current assignment is not a solution
  -- 8. if the empty assignment is not a solution there are no solutions
  -- 9. otherwise use the assignment that doesnt result in an empty clause
  sorry -- Full proof to be implemented

def fullresolve (l : List Clause) : List Clause :=
  let ls := literalset l;
  Nat.repeat (fun acc => let l' := simplify2 acc;
  if [] ∈ l' then acc else resolve2 acc ) ls.length (simplify3 l)

def solvable2 (l : List Clause) : Bool :=
  let ex := fullresolve l;
   !([] ∈ ex)

def fullresolvebit (l : List Clause) : List Clause :=
  let ls := literalset l;
  ls.foldl (fun acc n => let l' := simplify2 acc;
  if [] ∈ l' then acc else resolve2bit n acc)  (simplify3 l)

def solvable2bit (l : List Clause) : Bool :=
  let ex := fullresolvebit l;
   !([] ∈ ex)

--     Theorem stating that the `solvable1` and `solvable2` functions are equivalent.
--     This theorem states that for all inputs `l` (a list of clauses), the result of applying
--     `solvable1` is the same as the result of applying `solvable2`.
--     This means that both algorithms correctly determine whether a formula is satisfiable,
--     despite using different approaches to solve the problem.
theorem solvable1_equiv_solvable2 (l : List Clause) :
     solvable1 l = solvable2 l := by
     -- Proof sketch:
     -- 1. Both functions determine satisfiability of a list of clauses
     -- 2. solvable1 uses a recursive approach with unit propagation and case splitting
     -- 3. solvable2 uses repeated application of simplify2 and resolve2
     -- 4. Both approaches are sound and complete for SAT solving
     -- 5. For any list of clauses l:
     --    a. If l is satisfiable, both functions will return true
     --    b. If l is unsatisfiable, both functions will return false
     -- 6. Therefore, for all inputs l, solvable1 l = solvable2 l
  sorry -- Full proof to be implemented

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

--  Finds 3-clauses whose negation contradicts the input clauses.
--  This function:
--  1. Identifies all 3-clauses from the input
--  2. For each 3-clause, negates it and checks if the negation leads to a contradiction
--     when combined with the original clauses using unit propagation
--  3. Returns the list of distinct 3-clauses that satisfy this condition
-- @param clauses The list of input clauses
--  @return A list of distinct 3-clauses whose negation contradicts the input clauses
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

def find3clausesbit (n : Nat)(clauses : List Clause) : List Clause :=
  let find3 := find3ClausesWithContradiction clauses;
  find3.filter (fun clause => clause.any (fun lit => lit.1 = n))

def saturate (l : List Clause) : List Clause :=
  simplify2 (Nat.repeat (fun acc =>
    let negatedClauses := find3ClausesWithContradiction acc;
    if [] ∈ simplify2 acc then acc else
    negatedClauses ∪ acc) ((literalset l).length ) l)

def solvable3 (l : List Clause) : Bool :=
  [] ∉ simplify2 (saturate l)

def saturatebit (l : List Clause) : List Clause :=
  let ls := literalset l;
  simplify2 (ls.foldl (fun acc n =>
     if [] ∈ simplify2 acc
    then acc
    else (find3clausesbit n acc) ∪ acc)
  l)

def solvable3bit (l : List Clause) : Bool :=
  [] ∉ simplify2 (saturatebit l)

theorem fullresolve2clausesubsaturate2clause (l : List Clause) :
  find2ClausesWithContradiction (fullresolve l) ⊆ find2ClausesWithContradiction (saturate l) :=
  by
  sorry

theorem saturate2clausesubfullresolve2clause (l : List Clause) :
  find2ClausesWithContradiction (saturate l) ⊆ find2ClausesWithContradiction (fullresolve l) :=
  by
  sorry

theorem find2clausessubsetemptyinsimplifyimp (l1 l2 : List Clause) :
find2ClausesWithContradiction l1 ⊆ find2ClausesWithContradiction l2 -> ([] ∈ simplify2 l1 -> [] ∈ simplify2 l2) :=
  by
  sorry

theorem solvable3_equiv_solvable2 (l : List Clause) :
  solvable3 l = solvable2 l := by
  -- Proof sketch:
  -- 1. for any instance, its unsatisfiability(by solvable2) is equivalent to the set of 3clauses implied
  --   after the generation of all resolvents being the set of all 3clauses
  -- 2. then the unsatisfiability of the instance is equivalent to the set of 3clauses implied being the set of all 3clauses before gernerating any resolvents
  -- 3. the set of all 3clauses is unsatisfiable (by simplify2)
  -- 4. the set of all 3-clauses together with l is unsatisfiable (by solvable2)
  sorry -- Full proof to be implemented

theorem solvable3_ex (l : List Clause) :
  solvable3 l <-> (∃ (s : List (Nat × Bool)), (∀ l1 ∈ s,∀ l2 ∈ s, l1.1 = l2.1 -> l1.2 = l2.2) ∧ (clausetoformulaa toProp s ->
  clausesToFormula toProp l)) := by
  -- Proof sketch:
  -- 1. If the list of clauses is empty, it is trivially satisfiable.
  -- 2. If the list contains an empty clause, it is unsatisfiable.
  -- 3. The function uses unit propagation and resolution to simplify the clauses.
  -- 4. If a unit clause is found, it assigns a truth value to the variable and continues.
  -- 5. The function explores both possible assignments (true/false) for each variable.
  -- 6. If a satisfying assignment is found, it returns true; otherwise, false.
  -- 7. The equivalence follows from the definition of satisfiability and the operations performed.
  sorry -- Full proof to be implemented

--end Polysat2
