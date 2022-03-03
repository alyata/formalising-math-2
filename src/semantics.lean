import formula
import logic.nonempty

/-- A frame is a binary *accesibility* relation R on a nonempty set of *worlds*
W. -/
structure frame : Type 1 :=
  (W : Type) [hnonempty : nonempty W]
  (R : W → W → Prop)
notation `‹` W `, ` R `›` := frame.mk W R

instance frame_nonempty := frame.hnonempty

/-- A model for the language of modal formulas defined above is ⟨W, R, V⟩ 
where
1. W is a nonempty set of *worlds*,
2. R is a binary *accessibility* relation on W,
3. V is a truth assignment of each variable x to the set worlds in which it
   is true.
(W, R) alone without the truth assignment constitutes a `frame`. This separation
will become important when we talk about frame definability.

The nonemptiness of W will be assumed in the theorems, not the definition.

Note: W is given as an argument to deal with type universe issues. -/
structure model (vars : Type) : Type 1 :=
  (F : frame)
  (V : vars → set F.W)
notation `⟪` W `, ` R `, ` V `⟫` := model.mk (frame.mk W R) V 
notation `⟪` F `, ` V `⟫` := model.mk F V

@[ext]
lemma model_ext {vars : Type} (M : model vars)
: M = model.mk (frame.mk M.F.W M.F.R) M.V :=
begin
  rcases M with ⟨⟨W, _, R⟩, V⟩,
  simp
end

variables {vars : Type} [denumerable vars] {W : Type} [nonempty W]
variables {A B C : form vars}

/-- Truth at a world -/
@[simp]
def eval (M : model vars) : M.F.W → form vars → Prop
| w (form.Bottom) := false
| w ⦃x⦄ := w ∈ M.V x
| w (~ P) := ¬ eval w P
| w (P ⋀ Q) := eval w P ∧ eval w Q
| w (P ⋁ Q) := eval w P ∨ eval w Q
| w (P ⟹ Q) := eval w P → eval w Q
| w (□ P) := ∀ w', M.F.R w w' → eval w' P

notation M `@@` w ` ⊩ ` P := eval M w P
notation M `@@` w ` ⊮ ` P := ¬ eval M w P

theorem box_diamond_dual {M : model vars} {w : M.F.W}
  : (M @@ w ⊩ □ A) ↔ (M @@ w ⊩ ~ ◇ ~ A) :=
begin
  simp [eval],
end

theorem diamond_box_dual {M : model vars} {w : M.F.W}
  : (M @@ w ⊩ ◇ A) ↔ (M @@ w ⊩ ~ □ ~ A) :=
begin
  simp,
end

notation M ` ⊩ ` P := ∀w, M @@ w ⊩ P
notation M ` ⊮ ` P := ¬ (M ⊩ P)

example {M : model vars} : (M ⊩ A) → (M ⊮ ~ A) :=
begin
simp only [eval, not_forall, not_not],
intro hA,
use classical.choice M.F.hnonempty,
apply hA,
end

example {M : model vars} : (M ⊩ A ⟹ B) → (M ⊩ A) → (M ⊩ B) :=
begin
simp only [eval],
intros hAB hA w,
specialize hAB w,
specialize hA w,
exact hAB hA
end

def valid (A : form vars) := ∀ M : model vars, M ⊩ A

/- The following development of tautological instances is subsumed by a more
general proof when I talk about schemas, so I don't talk about it in the report.
I still learned something out of it though, so I'll leave it in. -/

/-- A formula is modal-free if it contains no modal operator, i.e. □ -/
def modal_free : form vars → Prop
| form.Bottom := true
| ⦃_⦄ := true
| ~ A := modal_free A
| (A ⋀ B) := modal_free A ∧ modal_free B
| (A ⋁ B) := modal_free A ∧ modal_free B
| (A ⟹ B) := modal_free A ∧ modal_free B
| □ A := false

/-- Modal-free formulas can be evaluated as they would in propositional logic, 
by truth-value assignments.

Learning point: recursing over two arguments to ensure that we can rule out 
the modality. -/
def eval_modal_free (v : vars → Prop) : ∀(A : form vars), modal_free A → Prop
| form.Bottom _ := false
| ⦃x⦄ _ := v x
| (~ A) hA := ¬ eval_modal_free A hA
| (A ⋀ B) ⟨hA, hB⟩ := eval_modal_free A hA ∧ eval_modal_free B hB
| (A ⋁ B) ⟨hA, hB⟩ := eval_modal_free A hA ∨ eval_modal_free B hB
| (A ⟹ B) ⟨hA, hB⟩ := eval_modal_free A hA → eval_modal_free B hB
| (□ A) hfalse := by {exfalso, exact hfalse}

/-- A modal-free formula is a tautology iff it is true under all 
truth-assignments. However, this notion is not well-defined for formulas 
containing □ as it depends on the truth-assignment over multiple worlds. -/
def tautology (A : form vars) (hfree : modal_free A) :=
∀ v, eval_modal_free v A hfree

/-- Instead we define a notion of tautological instance, which is a formula that is a substitution instance of some tautology. -/
def tautological_instance (A : form vars) := 
∃ Afree s (hfree : modal_free Afree), 
  tautology Afree hfree ∧ subst.apply s Afree = A

lemma eval_modal_free_iff_eval {hfree : modal_free A} {s : subst vars}
{v : vars → Prop} {M : model vars} {w : M.F.W}
(h : ∀ x, v x ↔ M@@w ⊩ s.get x)
  : eval_modal_free v A hfree ↔ M@@w ⊩ s.apply A :=
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

/-- It is quite sensible that since a tautology is valid, all tautological instances are also valid. -/
theorem tautological_instance_is_valid (ht : tautological_instance A) : valid A :=
begin
  -- Suppose for a contradiction that for some model M and world w,
  -- M@@w ⊭ A.
  by_contra,
  simp only [valid, not_forall, exists_prop] at h,
  rcases h with ⟨M, w, h⟩,
  -- Since A is a tautological instance, it is a substituition instance of some
  -- modal-free tautology Afree.
  rcases ht with ⟨Afree, s, hfree, htaut, hsubstAfree⟩,
  -- Define v(x) to be true iff whatever x substitutes into is true at w.
  set v := λ x, M@@w ⊩ s.get x,
  have hv : ∀ x, v x ↔ M@@w ⊩ s.get x, {
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

def entails (Γ : list (form vars)) (A : form vars) : Prop := 
∀ (M : model vars) w, (∀ (B ∈ Γ), (M@@w ⊩ B)) → M@@w ⊩ A

notation Γ ` ⊨ ` A := entails Γ A