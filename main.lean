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

/- Get the return value of a tactic without its side effects -/
meta def tactic.value_only {α : Type u} (t : tactic α) : tactic α :=
  λ ts,
    match t ts with
    | (result.success val _) := result.success val ts
    | (result.exception msg ref _) := result.exception msg ref ts
    end

/- Helper function for unify_with_args -/
private meta def unify_with_args_inner : expr → expr → list expr → tactic (option (list expr)) :=
λ fixed_type add_args_type accum_arg_types, do
  can_unify ← tactic.will_succeed $ tactic.unify fixed_type add_args_type,
  if can_unify then
    tactic.value_only $ do
      tactic.unify fixed_type add_args_type,
      substituted_arg_types ← monad.sequence $ accum_arg_types.reverse.map tactic.instantiate_mvars,
      return $ some substituted_arg_types
  else
    match add_args_type with
    | (expr.pi arg_name _ arg_type body) := do
        arg_mvar ← tactic.mk_meta_var arg_type,
        let substituted_expr := body.instantiate_var arg_mvar,
        unify_with_args_inner fixed_type substituted_expr (arg_type :: accum_arg_types)
    | _ := return none
    end

/-
Add arguments to `add_args_type` so it unifies with `fixed_type`
Returns `some [T1, T2, ..., Tn]` if unifiable after putting in arguments of types T1, T2, ..., Tn
Returns `none` if fails to unify
-/
meta def unify_with_args (fixed_type add_args_type : expr) : tactic (option (list expr)) :=
  unify_with_args_inner fixed_type add_args_type []

@[hole_command]
meta def any_value_that_fits : hole_command :=
{ name   := "Anything",
  descr  := "Insert any value that, when inserted, typechecks",
  action := λ _, do
    tar ← tactic.target,
    env ← tactic.get_env,
    ans ← env.fold (return []) $ λ decl accum, (do
      accum_result ← accum,
      unify_with_args_result ← unify_with_args tar decl.type,
      return $
        match unify_with_args_result with
        | some arg_types :=
            let args := string.join (list.repeat " {! !}" arg_types.length) in
            ("(" ++ decl.to_name.to_string ++ args ++ ")", "") :: accum_result
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