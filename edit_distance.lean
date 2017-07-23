/-
Edit types from page 17 of slides at http://ndmitchell.com/downloads/slides-hoogle_finding_functions_from_types-16_may_2011.pdf

Alias following: TODO use reduction somehow? zeta reduction?
Instances: Probably a special case of argument deletion
Subtyping: TODO How to implement this?
Boxing: TODO
Free variable duplication: TODO what is this?
Restriction: TODO
Argument deletion: apply_pi_type & unapply_pi_type
Argument reordering: TODO
-/

universe u

-- TODO is there an library function for this?
def option.to_list {α : Type u} : option α → list α
| (some x) := [x]
| none := []

/-
Given a type, find what type would result after applying it to a local_const argument, returning `none` if not a pi type
Equivalent to deleting an argument in a non-dependent type system
-/
private meta def apply_pi_type : expr → tactic (option expr)
| (expr.pi arg_name bi arg_type body_type) := do
  -- TODO: Maybe use mvar instead of local_const
  arg_local_const ← tactic.mk_local' arg_name bi arg_type,
  return $ some $ expr.instantiate_local arg_name arg_local_const body_type
| _ := return none

/-
Reverse of apply_pi_type
TODO (instantiate_local might be useful)
-/
private meta def unapply_pi_type : expr → tactic (list expr) := sorry

/-
Find all possible one-step edits from a type
Used for calculating edit distance
-/
meta def type_edits : expr → tactic (list expr) := λ ty, do
  apply_pi_type_result ← option.to_list <$> apply_pi_type ty,
  recurse_result ←
    match ty with
    -- TODO deal with other constructors of expr
    | (expr.app ty₁ ty₂) := do
      result₁ ← list.map (λ x, expr.app x ty₂) <$> type_edits ty₁,
      result₂ ← list.map (λ x, expr.app ty₁ x) <$> type_edits ty₂,
      return $ result₁ ++ result₂
    | _ := return []
    end,
  return $ apply_pi_type_result ++ recurse_result

/-
Checks if two types are equal for the purposes of edit distance
TODO
-/
meta def are_equal_types : expr → expr → tactic bool := sorry