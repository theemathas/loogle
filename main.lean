import .logging

universe u

/- Checks if applying a tactic will succeed without actually applying it -/
meta def tactic.will_succeed {α : Type u} (t : tactic α) : tactic bool :=
  λ ts,
    let b :=
      match t ts with
      | (result.success _ _) := tt
      | (result.exception _ _ _) := ff
      end
    in result.success b ts

/-
Returns `some n` if can fit after putting in `n` arguments
Returns `none` if cannot fit
-/
meta def fit_num : expr → expr → tactic (option ℕ) := λ hole_type test_type, do
  can_unify ← tactic.will_succeed $ tactic.unify hole_type test_type,
  if can_unify then
    return (some 0)
  else
    match test_type with
    | (expr.pi arg_name _ arg_type body) := do
        arg_mvar ← tactic.mk_meta_var arg_type,
        let substituted_expr := body.instantiate_var arg_mvar,
        recur_result ← fit_num hole_type substituted_expr,
        return $ match recur_result with
        | some n := some (n + 1)
        | none := none
        end
    | _ := return none
    end

@[hole_command]
meta def any_value_that_fits : hole_command :=
{ name   := "Anything",
  descr  := "Insert any value that, when inserted, typechecks",
  action := λ _, do
    tar ← tactic.target,
    env ← tactic.get_env,
    ans ← env.fold (return []) $ λ decl accum, (do
      accum_result ← accum,
      --if not (decl.to_name.to_string = "unsigned_sz") then return accum_result else do
      --if not (decl.to_name.to_string = "MyType.constr") then return accum_result else do
      fit_num_result ← fit_num tar decl.type,
      return $
        match fit_num_result with
        | some n := ("(" ++ decl.to_name.to_string ++ string.join (list.repeat " {! !}" n) ++ ")", "") :: accum_result
        | none := accum_result
        end
    ),
    log $ string.intercalate "\n" $ ans.map to_string,
    return ans
}

-- Applying hole command inserts `(unsigned_sz)`, which is a ℕ
example := 1 + {! !}

inductive MyType : ℕ → ℕ → Type
| constr : ∀ x y : ℕ, MyType x y

-- Applying hole command should insert `(MyType.constr {! !} {! !})`
-- Doesn't work yet
example : MyType 1 2 := {! !}

-- Doesn't work yet
example (x y z : ℕ) : ((x + y) + z = x + (y + z)) := {! !}

-- Doesn't work yet
example (α : Type u) (x : α) : α := {! !}