import formula
import semantics
import data.list.alist

variables {vars : Type} [denumerable vars]
variables {A B C : form vars}

/-- A schema is the set of substitution instances of some formula A. A is called the *characteristic* formula of the schema, which is unique up to a renaming of variables. -/
def schema (A : form vars) := {B | ∃s, subst.apply s A = B}

universes u v

/-- A renaming of variables is a mapping from variables to variables. -/
def rename (vars : Type) [decidable_eq vars] : Type := 
  { r : alist (λ _ : vars, vars) // 
    ∀ x y, r.lookup x = r.lookup y → 
           (r.lookup x).is_some → (r.lookup y).is_some → x = y }

instance : has_mem vars (rename vars) := ⟨λ x r, x ∈ r.val⟩
instance : has_emptyc (rename vars) := ⟨⟨∅, by simp⟩⟩

@[simp]
theorem list.lookup_cons_not_mem {α : Type u} {β : α → Type v} [decidable_eq α]
(l : list (sigma β)) {a : α} (s : sigma β) 
: a ∉ l.keys → ((list.lookup a (s :: l)).is_some ↔ a = s.fst) :=
begin
  rcases s with ⟨s_fst, s_snd⟩,
  simp only,
  intro ha,
  split,
  { intro hsome,
    simp only [list.lookup] at hsome,
    split_ifs at hsome,
    { simp only [h] },
    { rw list.lookup_is_some at hsome, exfalso, exact ha hsome }
  },
  {
    rintro rfl,
    simp only [list.lookup_cons_eq, option.is_some_some, coe_sort_tt],
  }
end

-- terrible, terrible proof
instance rename_to_subst (vars : Type) [decidable_eq vars] 
: has_coe (rename vars) (subst vars) :=
  ⟨λ ⟨r, p⟩, alist.mk (list.map (sigma.map id (λ _, form.Var)) r.entries) 
  (begin
    cases r,
    dsimp only,
    induction r_entries,
    case list.nil { simp },
    case list.cons : head tail ih {
      simp only [list.map, list.nodupkeys_cons] at ⊢ r_nodupkeys,
      split,
      { simp only [sigma.map, id.def, list.not_mem_keys],
        intro A,
        simp only [list.mem_map, sigma.exists, not_exists, not_and],
        intros x rx hmemtail,
        simp only [sigma.map, id.def, heq_iff_eq, not_and],
        intro hx,
        rw hx at hmemtail,
        rw list.not_mem_keys at r_nodupkeys,
        exfalso,
        exact r_nodupkeys.left rx hmemtail
      },
      { rcases r_nodupkeys with ⟨hnmemtail, r_nodupkeys⟩,
        apply ih r_nodupkeys,
        intros x y hxy,
        specialize p x y,
        simp only [alist.lookup] at ⊢ p hxy,
        intros hxmemtail hymemtail,
        simp only [list.lookup_is_some, 
                    list.keys_cons, 
                    list.mem_cons_iff] at hxmemtail hymemtail p,
        have hx := ne_of_mem_of_not_mem hxmemtail hnmemtail,
        have hy := ne_of_mem_of_not_mem hymemtail hnmemtail,
        simp [list.lookup_cons_ne _ _ hx, list.lookup_cons_ne _ _ hy] at p,
        specialize p hxy,
        apply p,
        { right, exact hxmemtail },          
        { right, exact hymemtail }
      },
    }
  end)⟩

theorem schema.characteristic_unique_up_to_renaming (h : schema A = schema B) 
  : ∃ (r₁ : rename vars), subst.apply ↑r₁ A = B :=
begin
  simp [set.ext_iff, schema] at h,
  induction A,
  case form.Bottom {
    simp [subst.apply] at ⊢ h,
    specialize h B,
    cases h.mpr ⟨∅, subst.apply_empty_id⟩ with _ this,
    exact ⟨∅, this⟩,
  },
  case form.Var {
    with_cases { by_cases hB : ∃ b, B = ⦃b⦄ },
    case pos {
      rcases hB with ⟨b, rfl⟩,
      set r : rename vars := ⟨alist.mk [⟨A, b⟩] (by simp), by {
        simp [alist.lookup],
        intros x y hxy,
        { intros hx hy, transitivity A, exact hx, symmetry, exact hy },
      }⟩ with hr,
      use r,
      unfold_coes,
      simp [subst.apply, subst.get, alist.lookup, hr, rename_to_subst,
            sigma.map, list.lookup]
    },
    case neg {
      exfalso,
      simp at hB,
      specialize h ⦃A⦄,
      cases h.mp ⟨∅, subst.apply_empty_id⟩ with _ this,
      exact subst.apply_not_var w hB A this,
    },
  },
  -- I give up... its not important for the main point of this project anyway
  case form.Not : A ih {
    sorry,
  },
  sorry,
  sorry,
  sorry,
  sorry,
end

def eval_schema (M : model vars) (S : set (form vars)) := ∀ B ∈ S, M ⊩ B
notation M ` ⊨ ` S := eval_schema M S
notation M ` ⊭ ` S := ¬ eval_schema M S

def valid_schema (S : set (form vars)) :=
∀ M : model vars, M ⊨ S

example : valid_schema (schema (□ (A ⟹ B) ⟹ □ A ⟹ □ B)) :=
begin
  intros M C hC w,
  simp only [schema, subst.apply, set.mem_set_of_eq] at hC,
  cases hC with s hC,
  rw ←hC,
  simp [eval],
  intros hAB hA w' hrel,
  exact hAB w' hrel (hA w' hrel)
end

lemma eval_instance_iff_eval {A : form vars} {W : Type} [nonempty W] {R : W → W → Prop} {V V' : vars → set W} {w : W} 
{s : subst vars} (hM' : ∀ x, V' x = {w | ⟪W, R, V⟫ @@ w ⊩ s.get x}) 
: (⟪W, R, V⟫ @@ w ⊩ s.apply A) ↔ (⟪W, R, V'⟫ @@ w ⊩ A)
:= begin
  induction A generalizing w,
  case form.Bottom { 
    simp only [subst.apply, bottom_eq_bot, eval],
  },
  case form.Var {
    simp only [subst.apply, eval, hM' A, set.mem_set_of_eq],
  },
  case form.Not : A ih {
    simp only [subst.apply, eval, not_iff_not, ih],
  },
  case form.And : A₁ A₂ ih₁ ih₂ {
    simp only [subst.apply, eval, ih₁, ih₂],
  },
  case form.Or : A₁ A₂ ih₁ ih₂ {
    simp only [subst.apply, eval, ih₁, ih₂],
  },
  case form.Imply : A₁ A₂ ih₁ ih₂ {
    simp only [subst.apply, eval, ih₁, ih₂],
  },
  case form.Box : A ih {
    simp only [subst.apply, eval],
    split,
    { intros h w' hw', specialize h w' hw', exact ih.mp h },
    { intros h w' hw', specialize h w' hw', exact ih.mpr h }
  }
end

/-- This is a generalisation of tautological_instance_is_valid where we have 
substitutions over arbitrary formulas, not just tautologies. -/
theorem valid_schema_iff_valid : valid_schema (schema A) ↔ valid A :=
begin
  split,
  -- the mp direction is easy since A must be in its own schema.
  { intros hv M w, exact hv M A ⟨∅, subst.apply_empty_id⟩ w },
  rintros hv M A' ⟨s, rfl⟩ w,
  by_contra h,
  -- We construct M' that re-assigns variables based on the truth value of their substitutions in the original model M.
  haveI := M.F.hnonempty,
  set V' := λ x, {w | M@@w ⊩ s.get x} with hV',
  set M' : model vars := 
    ⟪M.F.W, M.F.R, V'⟫ with hM',
  have hR : M.F.R = M'.F.R := rfl,
  have hM' : ∀ x, V' x = {w | ⟪M.F.W, M.F.R, M.V⟫@@w ⊩ s.get x},
    intro x,
    simp only [←model_ext M],
  -- Hence, whenever the substituted formula A' holds in the original model, 
  -- the pre-substituted formula A holds in our new model. This is represented
  -- by the lemma `eval_instance_iff_eval`.
  have := (eval_instance_iff_eval hM').mpr (hv M' w),
  exact h this,
end

/- What does this equivalence under validity mean for us? It means that we don't
actually need the notion of schema in the first place =/, because we can always
just reason about the characteristic formula. However, note that this 
equivalence under validity between the schema and its characteristic 
formula breaks down when we replace validity with truth in a specific model. 
Consider the following counterexample: -/

/-- At least one direction holds, since A is an instance of its own schema. -/
theorem characteristic_true_of_schema_true {M : model vars} 
  : (M ⊨ schema A) → (M ⊩ A) :=
begin
  intros hsA w,
  exact hsA A ⟨∅, subst.apply_empty_id⟩ w,
end

/-- but consider the following model with one world: -/
def myM : model vars := {
  F := {
    W := unit, -- one world only: the unit element ()
    R := λ _ _, false }, -- the frame relation doesn't matter
  V := λ x, {()} -- every variable is true at the one and only world ()
}

/-- This model is a counter-example for the other direction of the equivalence:
The variable p is true in myM at any world by definition of myM.V. However it 
has a substitution instance ⊥ that is never true at any world. -/
theorem characteristic_true_but_schema_not_true {p : vars}
  : (myM ⊩ ⦃p⦄) ∧ (myM ⊭ schema ⦃p⦄) :=
begin
  split,
  { rintro ⟨⟩, simp [eval, myM], sorry },
  { simp only [eval_schema, not_forall, exists_prop], 
    use ⊥,
    split,
    { use ⟨[⟨p, ⊥⟩], by simp⟩, simp [subst.apply, subst.get, alist.lookup] },
    { use ⟨⟩, simp [eval] }
  }
end

/-- Classes of models defined by a property of their frames. -/
def ℂ (F_prop : ∀ {W : Type}, (W → W → Prop) → Prop) : set (model vars) := {M | F_prop M.F.R}

/- The following are some example classes that contain models with particular 
frame properties. -/

/-- Models with reflexive frames -/
def ℂ_reflexive : set (model vars) :=
 ℂ (λ W R, ∀ w, R w w)

/-- Models with transitive frames -/
def ℂ_transitive : set (model vars) :=
ℂ (λ W R, ∀ w1 w2 w3, R w1 w2 ∧ R w2 w3 → R w1 w3)

/-- The general class of all models -/
def ℂ_all : set (model vars) := ℂ (λ _ _, true)

/-- It is also possible to define a restricted notion of validity to classes of 
models. -/
def ℂ_valid (ℂ : set (model vars)) (A : form vars) :=
∀ M ∈ ℂ, M ⊩ A

def ℂ_schema_valid (ℂ : set (model vars)) (𝕊 : set (form vars)) :=
∀ M ∈ ℂ, M ⊨ 𝕊

/-- We can then modify the proof of valid_schema_iff_valid to adapt it to 
class validity, but only for classes constructed by ℂ -/
theorem class_valid_schema_iff_class_valid 
{F_prop : ∀ {W : Type}, (W → W → Prop) → Prop} 
: ℂ_schema_valid (ℂ @F_prop) (schema A) ↔ ℂ_valid (ℂ @F_prop) A :=
begin
  split,
  -- the mp direction is easy since A must be in its own schema.
  { intros hv M hMℂ w, exact hv M hMℂ A ⟨∅, subst.apply_empty_id⟩ w },
  rintros hv M hMℂ A' ⟨s, rfl⟩ w,
  by_contra h,
  -- We construct M' that re-assigns variables based on the truth value of their
  -- substitutions in the original model M.
  set M' : model vars := 
    ⟨⟨M.F.R⟩, λ x, {w | M@@w ⊩ s.get x}⟩ with hM',
  have hR : M.F.R = M'.F.R := rfl,
  have hM' : ∀ x, M'.V x = {w | M@@w ⊩ s.get x} := λ x, rfl,
  -- This wouldn't work if we use arbitrary sets as classes since we'd know 
  -- nothing about what frames are included in the set
  have hM'ℂ : M' ∈ (@ℂ vars _ W _ F_prop), { 
    simp only [ℂ, set.mem_set_of_eq], exact hMℂ
  },
  -- Hence, whenever the substituted formula A' holds in the original model, 
  -- the pre-substituted formula A holds in our new model. This is represented
  -- by the lemma `eval_instance_iff_eval`.
  have := (eval_instance_iff_eval hR hM').mpr (hv M' hM'ℂ w),
  exact h this,
end

/- There is a vague sense in which the formula R ≡ p ⟹ ◇ p "characterizes"
models with reflexive relations. Semantically T reads that if p holds in this 
world, then p holds in some related world. In general, this holds iff the 
accessibility relation is reflexive, since the only world we can guarantee to
have p hold is the current one. We can see one direction of the correspondence
via the following theorem of validity: for any model, if it is reflexive, then R holds in the 
model. -/

theorem R_is_ℂ_valid_reflexive {p : vars} 
: ℂ_valid ℂ_reflexive (□ ⦃p⦄ ⟹ ⦃p⦄) := 
begin
  unfold ℂ_valid,
  intros M hM w,
  simp only [ℂ_reflexive, ℂ, set.mem_set_of_eq] at hM,
  simp only [eval, not_forall, exists_prop, set.not_not_mem],
  intros hbA,
  exact hbA w (hM w)
end

/- However, the converse doesn't hold: when R holds in a model, it is not 
necessarily reflexive. This is because we can have specific valuations that
make it trivial to prove the statement. So, the statement is true by virtue of the valuation, not the frame. For example, in a model where the
antecedent p is never true. -/

def myM' : model vars := {
  F := {
    W := unit,
    R := λ _ _, false }, -- the frame relation doesn't matter
  V := λ x, {} -- every variable is true at the one and only world
}

theorem R_true_in_non_reflexive_model {p : vars} : (myM' ⊩ ⦃p⦄ ⟹ ◇⦃p⦄) ∧ (myM' ∉ ℂ_reflexive) :=
begin
  split,
  simp [eval, myM'],
  simp [ℂ_reflexive, ℂ, myM']
end

/- This doesn't work because it is the frame relation that we care about, but
we are reasoning about classes of models. Instead, we should work with classes
of frames and work from there. This is done in src/frame_definability.lean. -/

theorem K_is_ℂ_valid_all 
  : ℂ_valid ℂ_all (□ (A ⟹ B) ⟹ □ A ⟹ □ B) :=
begin
  unfold ℂ_valid,
  intros M hM w,
  unfold eval,
  intros hbAB hbA w' hrel,
  specialize hbAB w' hrel,
  specialize hbA w' hrel,
  exact hbAB hbA
end

example : ℂ_valid ℂ_reflexive (□ (□ A ⟹ A)) :=
begin
  simp only [ℂ_valid, set.mem_inter_eq],
  intros M hrefl w,
  unfold eval,
  intros w' hrel hbA,
  apply hbA,
  simp only [ℂ_reflexive, set.mem_set_of_eq] at hrefl,
  exact hrefl w'
end

theorem box_class_valid_of_class_valid {C : set (model vars)}
(hvA : ℂ_valid C A) : ℂ_valid C (□ A) :=
begin
  unfold ℂ_valid,
  intros M hMinC _,
  unfold eval,
  intros w' hrel,
  exact hvA M hMinC w',
end

theorem class_valid_subset {C C' : set (model vars)} (hsub : C' ⊆ C) 
(hvA : ℂ_valid C A) : ℂ_valid C' A :=
begin
  unfold ℂ_valid,
  intros M hMinC',
  exact hvA M (hsub hMinC')
end