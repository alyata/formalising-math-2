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
instance {vars : Type} : has_bot (form vars) := ⟨form.Bottom⟩
-- and allow simp to unwrap this definition
@[simp] lemma bottom_eq_bot {vars : Type} : (form.Bottom : form vars) = ⊥ := rfl
notation `⦃` x `⦄` := form.Var x
prefix `~`:75 := form.Not
prefix `□`:75 := form.Box
infixl ` ⋀ `:70 := form.And
infixl ` ⋁ `:65 := form.Or
infixr ` ⟹ `:60 := form.Imply

prefix `◇`:75 := form.Not ∘ form.Box ∘ form.Not
@[simp] lemma diamond_eq_not_box_not {vars : Type} {A : form vars} 
  : ◇ A = ~ □ ~ A := rfl

variables {vars : Type} [denumerable vars]

instance vars_decidable_eq : decidable_eq vars := 
encodable.decidable_eq_of_encodable _

instance form_inhabited : inhabited (form vars) := ⟨form.Bottom⟩

/-- A simultaneous substitution on formulas is an association list (key-value)
mapping from variables to the formula that it should be substituted by.-/
def subst (vars : Type) : Type := alist (λ _ : vars, form vars)
-- can't resolve this implicitly for some reason, even after importing
instance : has_mem vars (subst vars) := alist.has_mem

/-- This function applies a simultaneous substitution to a formula. -/
def subst.apply (s : subst vars) : form vars → form vars
| ⊥        := ⊥
| ⦃x⦄      := (alist.lookup x s).get_or_else ⦃x⦄
| ~ A      := ~ (subst.apply A)
| □ A      := □ (subst.apply A)
| (A ⋀ B)  := (subst.apply A) ⋀ (subst.apply B)
| (A ⋁ B)  := (subst.apply A) ⋁ (subst.apply B)
| (A ⟹ B) := (subst.apply A) ⟹ (subst.apply B)  

/-- A frame is a binary *accesibility* relation R on a nonempty set of *worlds*
W. Separating this from the notion of a model will become important when we talk
about frame definability.

Note: W is given as an argument to deal with type universe issues. -/
structure frame (W : Type) [nonempty W] : Type :=
  (R : W → W → Prop)

/-- A model for the language of modal formulas defined above is ⟨W, R, V⟩ 
where
1. W is a nonempty set of *worlds*,
2. R is a binary *accesibility* relation on W,
3. V is a truth assignment of each variable x to the set worlds in which it
   is true.
(W, R) alone without the truth assignment constitutes a `frame`.

Note: W is given as an argument to deal with type universe issues. -/
structure model (vars : Type) (W : Type) [nonempty W] : Type :=
  (F : frame W)
  (V : vars → set W)

variables {W : Type} [nonempty W]
variables {A B C : form vars}

/-- Truth at a world -/
def eval (M : model vars W) : W → form vars → Prop
| w ⊥ := false
| w ⦃x⦄ := w ∈ M.V x
| w (~ P) := ¬ eval w P
| w (P ⋀ Q) := eval w P ∧ eval w Q
| w (P ⋁ Q) := eval w P ∨ eval w Q
| w (P ⟹ Q) := eval w P → eval w Q
| w (□ P) := ∀ w', M.F.R w w' → eval w' P

notation M `@@` w ` ⊨ ` P := eval M w P

theorem box_diamond_dual {M : model vars W} {w : W}
  : (M @@ w ⊨ □ A) ↔ (M @@ w ⊨ ~ ◇ ~ A) :=
begin
  simp [eval],
end

theorem diamond_box_dual {M : model vars W} {w : W}
  : (M @@ w ⊨ ◇ A) ↔ (M @@ w ⊨ ~ □ ~ A) :=
begin
  simp,
end

notation M ` ⊨ ` P := ∀w, M @@ w ⊨ P
notation M ` ⊭ ` P := ¬ (M ⊨ P)

example {M : model vars W} : (M ⊨ A) → (M ⊭ ~ A) :=
begin
simp only [eval, not_forall, not_not],
intro hA,
use _inst_2.some,
apply hA,
end

example {M : model vars W} : (M ⊨ A ⟹ B) → (M ⊨ A) → (M ⊨ B) :=
begin
simp only [eval],
intros hAB hA w,
specialize hAB w,
specialize hA w,
exact hAB hA
end

def valid (C : set (model vars W)) (A : form vars) :=
∀ M ∈ C, M ⊨ A

def class_reflexive (W : Type) [nonempty W] : set (model vars W) :=
{M | ∀ w, M.F.R w w}

def class_transitive (W : Type) [nonempty W] : set (model vars W) :=
{M | ∀ w1 w2 w3, M.F.R w1 w2 ∧ M.F.R w2 w3 → M.F.R w1 w3}

def class_all (W : Type) [nonempty W] : set (model vars W) := set.univ

theorem T_is_valid_reflexive : valid (class_reflexive W) (□ A ⟹ A) :=
begin
  unfold valid,
  intros M hM w,
  simp only [class_reflexive, set.mem_set_of_eq] at hM,
  simp only [eval, not_forall, exists_prop],
  intros hbA,
  apply hbA,
  exact hM w
end

theorem K_is_valid_all : valid (class_all W) (□ (A ⟹ B) ⟹ □ A ⟹ □ B) :=
begin
  unfold valid,
  intros M hM w,
  unfold eval,
  intros hbAB hbA w' hrel,
  specialize hbAB w' hrel,
  specialize hbA w' hrel,
  exact hbAB hbA
end

-- example : valid (class_reflexive W) (□ (□ A ⟹ A)) :=
-- begin
--   simp only [valid, set.mem_inter_eq],
--   intros M hrefl w,
--   unfold eval,
--   intros w' hrel hbA,
--   apply hbA,
--   simp only [class_reflexive, set.mem_set_of_eq] at hrefl,
--   exact hrefl w'
-- end

theorem box_valid_of_valid {C : set (model vars W)} (hvA : valid C A) 
  : valid C (□ A) :=
begin
  unfold valid,
  intros M hMinC _,
  unfold eval,
  intros w' hrel,
  exact hvA M hMinC w',
end

theorem valid_subset {C C' : set (model vars W)} (hsub : C' ⊆ C) (hvA : valid C A) 
  : valid C' A :=
begin
  unfold valid,
  intros M hMinC',
  exact hvA M (hsub hMinC')
end

def modal_free : form vars → Prop
| ⊥ := true
| ⦃_⦄ := true
| ~ A := modal_free A
| (A ⋀ B) := modal_free A ∧ modal_free B
| (A ⋁ B) := modal_free A ∧ modal_free B
| (A ⟹ B) := modal_free A ∧ modal_free B
| □ A := false

/-- Modal-free formulas can be evaluated as they would in propositional logic.
Learning point: recursing over two arguments to ensure that we can rule out 
the modality. -/
def eval_modal_free (v : vars → Prop) : ∀(A : form vars), modal_free A → Prop
| ⊥ _ := false
| ⦃x⦄ _ := v x
| (~ A) hA := ¬ eval_modal_free A hA
| (A ⋀ B) ⟨hA, hB⟩ := eval_modal_free A hA ∧ eval_modal_free B hB
| (A ⋁ B) ⟨hA, hB⟩ := eval_modal_free A hA ∨ eval_modal_free B hB
| (A ⟹ B) ⟨hA, hB⟩ := eval_modal_free A hA → eval_modal_free B hB
| (□ A) hfalse := by {exfalso, exact hfalse}

def tautology (A : form vars) (hfree : modal_free A) :=
∀ v, eval_modal_free v A hfree

def tautological_instance (A : form vars) := 
∃ Afree s (hfree : modal_free Afree), 
  tautology Afree hfree ∧ subst.apply s Afree = A

lemma eval_modal_free_iff_eval {hfree : modal_free A} {s : subst vars}
{v : vars → Prop} {M : model vars W} {w : W}
(h : ∀ x, v x ↔ M@@w ⊨ (s.lookup x).get_or_else ⦃x⦄)
  : eval_modal_free v A hfree ↔ M@@w ⊨ s.apply A :=
begin
  induction A,
  case form.Bottom {
    simp [eval_modal_free, subst.apply, eval]
  },
  case form.Var {
    rw [eval_modal_free, subst.apply],
    specialize h A,
    exact h,
  },
  case form.Not : A ih {
    rw [eval_modal_free, subst.apply, eval, ih],
  },
  case form.And : A₁ A₂ ih₁ ih₂ {
    rw [subst.apply, eval, ←ih₁, ←ih₂, ←eval_modal_free],
    refl,
    exact hfree.right,
    exact hfree.left
  },
  case form.Or : A₁ A₂ ih₁ ih₂ {
    rw [subst.apply, eval, ←ih₁, ←ih₂, ←eval_modal_free],
    refl,
    exact hfree.right,
    exact hfree.left
  },
  case form.Imply : A₁ A₂ ih₁ ih₂ {
    rw [subst.apply, eval, ←ih₁, ←ih₂, ←eval_modal_free],
    refl,
    exact hfree.right,
    exact hfree.left
  },
  case form.Box : A ih {
    -- well this case should never happen, really
    exfalso,
    exact hfree
  }
end

theorem tautological_instance_is_valid (ht : tautological_instance A) 
  : valid (class_all W) A :=
begin
  -- Suppose for a contradiction that for some model M and world w,
  -- M@@w ⊭ A.
  by_contra,
  simp only [valid, not_forall, exists_prop] at h,
  rcases h with ⟨M, hMinC, w, h⟩,
  -- Since A is a tautological instance, it is a substituition instance of some
  -- modal-free tautology Afree.
  rcases ht with ⟨Afree, s, hfree, htaut, hsubstAfree⟩,
  -- define v(x) to be true iff x appears in the substitution 
  set v := λ x, M@@w ⊨ ((s.lookup x).get_or_else ⦃x⦄),
  have hv : ∀ x, v x ↔ M@@w ⊨ (s.lookup x).get_or_else ⦃x⦄, {
    intro x,
    refl
  },
  -- since Afree is a tautology so it always evaluates to true, by the previous
  -- lemma we have that M@@w ⊨ A.
  have := (eval_modal_free_iff_eval hv).mp (htaut v),
  rw hsubstAfree at this,
  -- This contradicts with the initial assumption.
  exact h this,
end

def schema (A : form vars) := {B | ∃s, subst.apply s A = B}

def entails (Γ : list (form vars)) (A : form vars) : Prop := 
∀ (M : model vars W) w, (∀ (B ∈ Γ), (M@@w ⊨ B)) → M@@w ⊨ A

notation Γ ` ⊨ ` A := entails Γ A

