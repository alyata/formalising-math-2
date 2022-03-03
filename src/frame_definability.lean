import formula
import semantics
import schemas
import model_theory.basic
import model_theory.terms_and_formulas
import data.fin.basic
import data.fin.vec_notation

open first_order.language
open first_order.language.bounded_formula

variables {vars : Type} [denumerable vars] {W : Type} [nonempty W]
variables {A B C : form vars}

/-- Classes of models defined by a property of their frames. -/
def 𝔽 (F_prop : ∀ {W : Type}, (W → W → Prop) → Prop) : set frame :=
{F | F_prop F.R}

def 𝔽_reflexive : set frame :=
𝔽 (λ W R, ∀ w, R w w)

def 𝔽_transitive : set frame :=
𝔽 (λ W R, is_trans W R)

def 𝔽_euclidean : set frame :=
𝔽 (λ W R, ∀ u v w, R u v → R u w → R v w)

def 𝔽_converse_well_founded : set frame :=
𝔽 (λ W R, well_founded (flip R))

@[simp]
lemma 𝔽_reflexive_def (F : frame) : F ∈ 𝔽_reflexive ↔ ∀ w, F.R w w :=
by simp only [𝔽_reflexive, 𝔽, set.mem_set_of_eq] 

/-- A is true in a frame F iff M ⊩ A for every model M based on F. -/
def frame_eval (F : frame) (A : form vars) := ∀ V, ⟨F, V⟩ ⊩ A
notation F ` ⊩ ` A := frame_eval F A
notation F ` ⊮ ` A := ¬ frame_eval F A

theorem frame_eval_and (F : frame) : (F ⊩ A) ∧ (F ⊩ B) ↔ (F ⊩ A ⋀ B) :=
begin
  simp [frame_eval, ←forall_and_distrib],
end

/-- A is valid in a class of frames 𝔽 iff F ⊨ A for every frame F ∈ 𝔽. -/
def class_frame_valid (𝔽 : set frame) (A : form vars) := ∀ F ∈ 𝔽, F ⊩ A
notation 𝔽 ` ⊨ ` A := class_frame_valid 𝔽 A

def defines (A : form vars) (𝔽 : set frame) := 
∀ F, F ∈ 𝔽 ↔ (F ⊩ A)

theorem 𝔽_reflexive_is_definable {p : vars} 
: defines (□ ⦃p⦄ ⟹ ⦃p⦄) 𝔽_reflexive := 
begin
  intro F,
  simp only [𝔽_reflexive_def, diamond_eq_not_box_not],
  split,
  { -- This direction is easy: if □ p holds at w, then p holds at all worlds 
    -- related to w, which includes w itself by the reflexivity of R.
    intros hF V w,
    simp only [eval, not_forall, set.not_not_mem, exists_prop],
    intro hw,
    exact hw w (hF w)
  },
  { -- Suppose for a contradiction R is not reflexive
    intros hT w,
    by_contra,
    -- so we have a world w s.t. h : ¬ R w w.
    -- We want to contradict against hT, which states T is true at all worlds 
    -- under all valuations
    simp only [frame_eval, eval] at hT,
    -- so we need a valuation that falsifies T at some world.
    -- i.e. makes □ p true but p false at w (the only world we have in scope)
    -- Since ¬ R w w, w is not included in the following set so p is false at w
    -- However, □ p is true at w since p is true in all worlds related to w by
    -- construction.
    let V := λ _, {w' | F.R w w'},
    specialize hT V w,
    have := mt hT h,
    simp only [set.mem_set_of_eq, imp_self, forall_const, not_true] at this,
    exact this
  }
end

/-- Transitive frames are defined by formula 4 (name due to historical reasons)
-/
theorem 𝔽_transitive_is_definable {p : vars} 
: defines (◇ ◇ ⦃p⦄ ⟹ ◇ ⦃p⦄) 𝔽_transitive :=
begin
  intro F,
  split,
  { simp only [frame_eval, eval, not_forall, set.not_not_mem, exists_prop, 
               not_exists, not_and, forall_exists_index, and_imp],
    rintros ⟨hF⟩ V u v huv w hvw hw,
    use w,
    exact ⟨hF u v w huv hvw, hw⟩
  },
  { -- as before we prove by contradiction and forming a valuation that 
    -- falsifies the defining formula from the assumption that F is intransitive
    intros h4,
    refine ⟨_⟩,
    intros u v w huv hvw,
    by_contra,
    let V := λ _, {w}, -- so from world u, only ◇ ◇ p holds but not ◇ p since p 
                      -- is not true in v
    simp only [frame_eval, eval, not_forall, set.not_not_mem, exists_prop, 
               not_exists, not_and, forall_exists_index, and_imp] at h4,
    specialize h4 V u v huv w hvw (set.mem_singleton w),
    simp only [set.mem_singleton_iff, exists_eq_right] at h4,
    exact h h4
  }
end

/-- Euclidean frames are defined by formula 5 (again, historical reasons)-/
theorem 𝔽_euclidean_is_definable {p : vars} 
: defines (◇ ⦃p⦄ ⟹ □ ◇ ⦃p⦄) 𝔽_euclidean :=
begin
  intro F,
  split,
  { simp only [frame_eval, eval, not_forall, set.not_not_mem, exists_prop, forall_exists_index, and_imp],
    rintros hF V u w huw hw v huv,
    use w,
    exact ⟨hF u v w huv huw, hw⟩
  },
  { intros h5 u v w huv huw,
    by_contra,
    -- since ¬ F.R v w, w is in this set so ◇ p holds in u by virtue of R u w.
    -- However, by construction ◇ p does not hold in v as p is false in all the 
    -- worlds accessible from v, so □ ◇ p does not hold in u. 
    let V := λ_, {z | ¬ F.R v z},
    simp only [frame_eval, eval, not_forall, set.not_not_mem, exists_prop, 
               not_exists, not_and, forall_exists_index, and_imp] at h5,
    specialize h5 V u w huw h v huv,
    simp at h5,
    exact h5
  }
end

theorem 𝔽_inter {𝔽₁ 𝔽₂ : set frame} (h1 : defines A 𝔽₁) (h2 : defines B 𝔽₂)
: defines (A ⋀ B) (𝔽₁ ∩ 𝔽₂) :=
begin
  intro F,
  simp only [set.mem_inter_eq],
  rw [h1, h2],
  exact frame_eval_and F,
end

/-- The Lob formula characterise frames that are transitive and converse 
well-founded.-/
theorem 𝔽_transitive_converse_well_founded_is_definable {p : vars}
: defines (□ (□ ⦃p⦄ ⟹ ⦃p⦄) ⟹ □ ⦃p⦄) (𝔽_transitive ∩ 𝔽_converse_well_founded)
:= begin
  intro F,
  split,
  { intros hF V w,
    rcases hF with ⟨htrans, hwf⟩,
    simp [𝔽_converse_well_founded, 𝔽] at hwf,
    -- Supppose for a contradiction that the defining formula is not true in F
    by_contra,
    -- So we have a world w s.t. w ⊩ □ (□ p ⟹ p) but w ⊮ □ p
    unfold1 eval at h,
    simp only [not_forall, exists_prop] at h,
    rcases h with ⟨h1, h2⟩,
    -- From this, we can form an infinite chain w₁Rw₂... of worlds to
    -- contradict R's (converse) wellfoundness.
    -- Since w ⊮ □ p, w has an R-successor w₁ s.t.  w₁ ⊮ p.
    -- Since w ⊩ □ (□ p ⟹ p). w₁ ⊩ □ p ⟹ p. So by modus tolens, w₁ ⊮ □ p.
    -- Now we can repeat the argument: since wᵢ ⊮ □ p then wᵢ₊₁ ⊮ p for some
    -- successor wᵢ₊₁ of wᵢ. By transitivity, wᵢ₊₁ is also a successor of w so
    -- wᵢ₊₁ ⊩ □ p ⟹ p and hence we can conclude wᵢ₊₁ ⊮ □ p.

    -- To formalise this argument, we find a maximal world a satisfying the
    -- required conditions using the (converse) wellfoundness of R. We apply the
    -- inductive part of the argument to effectively show that since a = wᵢ for
    -- some i, then a' = wᵢ₊₁ is an R-successor of a, so in fact a is not the
    -- maximal world. This gives the required contradiction.
    haveI : is_trans F.W F.R := by { simp [𝔽_transitive, 𝔽] at htrans, exact htrans },
    -- the min of the flipped R is the max of R.
    obtain ⟨a, ha, hwf⟩ := 
      well_founded.has_min hwf 
      {u | F.R w u ∧
        (⟪F, V⟫@@u ⊩ □ ⦃p⦄ ⟹ ⦃p⦄) ∧
        (⟪F, V⟫@@u ⊮ (□ ⦃p⦄))} 
      -- the base case forms the proof of nonemptiness
      ⟨_, _⟩,
    rotate,

    -- The base case
    unfold1 eval at h2,
    simp only [not_forall, exists_prop] at h2,
    let w₁ := classical.some h2,
    exact w₁,
    unfold1 eval at h2,
    simp only [not_forall, exists_prop] at h2,
    obtain ⟨hww₁, h2⟩ := classical.some_spec h2,
    exact ⟨hww₁, h1 _ hww₁, mt (h1 _ hww₁) h2⟩,

    -- The inductive case 
    obtain ⟨hwa, ih1, ih2⟩ := ha,
    unfold1 eval at ih2, simp only [not_forall, exists_prop] at ih2,
    rcases ih2 with ⟨a', haa', ih2⟩,
    have hwa' := trans hwa haa',
    specialize hwf a' ⟨hwa', h1 a' hwa', mt (h1 a' hwa') ih2⟩,
    simp [inv_image, flip] at hwf,
    exact hwf haa',
  }, {
    sorry -- not enough time!
  }
end

/-- The first order frame language with one 2-ary relation symbol. -/
def L : first_order.language := {
  functions := λ _, empty,
  relations := λ n, match n with
    | 2 := unit
    | n := empty
  end
}

def realize_sentence' (M : L.Structure W) (S : L.sentence) 
:= realize_sentence W S

def first_order_definable (𝔽 : set frame) (S : L.sentence) :=
begin
  refine ∀ F, F ∈ 𝔽 ↔ _,
  let M : L.Structure F.W := {
    fun_map := λ n e args, empty.elim e, 
    rel_map := λ n t args, match n, args with
    | 2, args := F.R (args 0) (args 1)
    | n, args := false
    end
  },
  -- M ⊨ S
  exact realize_sentence' M S,
end

theorem 𝔽_reflexive_is_fodefinable : first_order_definable 𝔽_reflexive
(bounded_formula.all 
  (@relations.bounded_formula L empty 2 1 () 
    ![term.var (sum.inr 0), term.var (sum.inr 0)]))
:= begin
  -- It turns out you don't even need the simp...
  -- but I don't actualy understand what's going on unless I simp it so
  -- leave this here just in case.
  -- simp only [first_order_definable, realize_sentence', realize_sentence,
  --            formula.realize, realize_all, realize_rel, term.realize,
  --            matrix.cons_val_zero, sum.elim_inr, matrix.cons_val_one, 
  --            matrix.head_cons, 𝔽_reflexive, 𝔽, set.mem_set_of_eq],
  intro F,
  split,
  { intros hF, exact hF },
  { intros h, exact h }
end

/- The key reason for using this embedded first-order language is I wanted
to show that the converse-wellfounded + transitive class from before cannot
be defined by a first-order sentence. I never got around to it, but I still
learned about using lean's definitions for first-order logic.-/