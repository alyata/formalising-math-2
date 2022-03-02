import tactic
import data.list.alist
import data.equiv.denumerable
import data.equiv.encodable.basic

/-- Formulas of modal logic
form vars ∷= ⦃x : vars⦄ | ⊥ | ~ form | form ⋀ form | form ⋁ form -/
inductive form (vars : Type) : Type
| Bottom : form
| Var    : vars → form
| Not    : form → form
| And    : form → form → form
| Or     : form → form → form
| Imply  : form → form → form
| Box    : form → form

-- get the ⊥ notation for Bottom
-- and allow simp to use this definition
instance {vars : Type} : has_bot (form vars) := ⟨form.Bottom⟩
@[simp] lemma bottom_eq_bot {vars : Type} : ⊥ = (form.Bottom : form vars) := rfl

notation `⦃` x `⦄` := form.Var x
prefix `~`:75 := form.Not
prefix `□`:75 := form.Box
infixl ` ⋀ `:70 := form.And
infixl ` ⋁ `:65 := form.Or
infixr ` ⟹ `:60 := form.Imply

-- Since we intend to use a classical semantics, ◇ can be implemented in terms 
-- of □
prefix `◇`:75 := form.Not ∘ form.Box ∘ form.Not

@[simp] lemma diamond_eq_not_box_not {vars : Type} {A : form vars} 
  : ◇ A = ~ □ ~ A := rfl

variables {vars : Type} [denumerable vars]
variables {A B C : form vars}

instance vars_decidable_eq : decidable_eq vars := 
encodable.decidable_eq_of_encodable _

instance form_inhabited : inhabited (form vars) := ⟨form.Bottom⟩

/-- A simultaneous substitution on formulas is an association list (key-value)
mapping from variables to the formula that it should be substituted by.-/
def subst (vars : Type) : Type := alist (λ _ : vars, form vars)

-- can't resolve these implicitly for some reason, even after importing.
instance : has_mem vars (subst vars) := alist.has_mem
instance : has_emptyc (subst vars) := alist.has_emptyc

def subst.get (s : subst vars) (x : vars) : form vars := 
(s.lookup x).get_or_else ⦃x⦄

/-- This function applies a simultaneous substitution to a formula. -/
def subst.apply (s : subst vars) : form vars → form vars
| form.Bottom := form.Bottom
| ⦃x⦄      := s.get x
| ~ A      := ~ (subst.apply A)
| □ A      := □ (subst.apply A)
| (A ⋀ B)  := (subst.apply A) ⋀ (subst.apply B)
| (A ⋁ B)  := (subst.apply A) ⋁ (subst.apply B)
| (A ⟹ B) := (subst.apply A) ⟹ (subst.apply B)

theorem subst.apply_empty_id : subst.apply ∅ A = A :=
begin
  induction A,
  case form.Bottom { simp [subst.apply] },
  case form.Var { simp [subst.apply, subst.get] },
  case form.Not : A ih { simp [subst.apply, ih] },
  case form.Box : A ih { simp [subst.apply, ih] },
  case form.And : A B ihA ihB { simp [subst.apply, ihA, ihB] },
  case form.Or : A B ihA ihB { simp [subst.apply, ihA, ihB] },
  case form.Imply : A B ihA ihB { simp [subst.apply, ihA, ihB] }
end

theorem subst.apply_not_var (s : subst vars) {A : form vars} (hA : ∀ x, A ≠ ⦃x⦄) 
  : ∀ y, subst.apply s A ≠ ⦃y⦄ :=
begin
  intro y,
  induction A,
  case form.Bottom { exact hA y },
  case form.Var    { exfalso, specialize hA A, simp at hA, exact hA },
  case form.Not    { simp [subst.apply] },
  case form.Box    { simp [subst.apply] },
  case form.And    { simp [subst.apply] },
  case form.Or     { simp [subst.apply] },
  case form.Imply  {simp [subst.apply] }
end

theorem subst.apply_not_not (s : subst vars) {A : form vars} (hA : ∀ x, A ≠ ~ x) 
  : ∀ y, subst.apply s A ≠ ~ y :=
begin
  intro y,
  induction A,
  case form.Bottom { exact hA y },
  case form.Var    {  },
  case form.Not    { simp [subst.apply] },
  case form.Box    { simp [subst.apply] },
  case form.And    { simp [subst.apply] },
  case form.Or     { simp [subst.apply] },
  case form.Imply  {simp [subst.apply] }
end