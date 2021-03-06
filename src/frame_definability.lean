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
def ๐ฝ (F_prop : โ {W : Type}, (W โ W โ Prop) โ Prop) : set frame :=
{F | F_prop F.R}

def ๐ฝ_reflexive : set frame :=
๐ฝ (ฮป W R, โ w, R w w)

def ๐ฝ_transitive : set frame :=
๐ฝ (ฮป W R, is_trans W R)

def ๐ฝ_euclidean : set frame :=
๐ฝ (ฮป W R, โ u v w, R u v โ R u w โ R v w)

def ๐ฝ_converse_well_founded : set frame :=
๐ฝ (ฮป W R, well_founded (flip R))

@[simp]
lemma ๐ฝ_reflexive_def (F : frame) : F โ ๐ฝ_reflexive โ โ w, F.R w w :=
by simp only [๐ฝ_reflexive, ๐ฝ, set.mem_set_of_eq] 

/-- A is true in a frame F iff M โฉ A for every model M based on F. -/
def frame_eval (F : frame) (A : form vars) := โ V, โจF, Vโฉ โฉ A
notation F ` โฉ ` A := frame_eval F A
notation F ` โฎ ` A := ยฌ frame_eval F A

theorem frame_eval_and (F : frame) : (F โฉ A) โง (F โฉ B) โ (F โฉ A โ B) :=
begin
  simp [frame_eval, โforall_and_distrib],
end

/-- A is valid in a class of frames ๐ฝ iff F โจ A for every frame F โ ๐ฝ. -/
def class_frame_valid (๐ฝ : set frame) (A : form vars) := โ F โ ๐ฝ, F โฉ A
notation ๐ฝ ` โจ ` A := class_frame_valid ๐ฝ A

def defines (A : form vars) (๐ฝ : set frame) := 
โ F, F โ ๐ฝ โ (F โฉ A)

theorem ๐ฝ_reflexive_is_definable {p : vars} 
: defines (โก โฆpโฆ โน โฆpโฆ) ๐ฝ_reflexive := 
begin
  intro F,
  simp only [๐ฝ_reflexive_def, diamond_eq_not_box_not],
  split,
  { -- This direction is easy: if โก p holds at w, then p holds at all worlds 
    -- related to w, which includes w itself by the reflexivity of R.
    intros hF V w,
    simp only [eval, not_forall, set.not_not_mem, exists_prop],
    intro hw,
    exact hw w (hF w)
  },
  { -- Suppose for a contradiction R is not reflexive
    intros hT w,
    by_contra,
    -- so we have a world w s.t. h : ยฌ R w w.
    -- We want to contradict against hT, which states T is true at all worlds 
    -- under all valuations
    simp only [frame_eval, eval] at hT,
    -- so we need a valuation that falsifies T at some world.
    -- i.e. makes โก p true but p false at w (the only world we have in scope)
    -- Since ยฌ R w w, w is not included in the following set so p is false at w
    -- However, โก p is true at w since p is true in all worlds related to w by
    -- construction.
    let V := ฮป _, {w' | F.R w w'},
    specialize hT V w,
    have := mt hT h,
    simp only [set.mem_set_of_eq, imp_self, forall_const, not_true] at this,
    exact this
  }
end

/-- Transitive frames are defined by formula 4 (name due to historical reasons)
-/
theorem ๐ฝ_transitive_is_definable {p : vars} 
: defines (โ โ โฆpโฆ โน โ โฆpโฆ) ๐ฝ_transitive :=
begin
  intro F,
  split,
  { simp only [frame_eval, eval, not_forall, set.not_not_mem, exists_prop, 
               not_exists, not_and, forall_exists_index, and_imp],
    rintros โจhFโฉ V u v huv w hvw hw,
    use w,
    exact โจhF u v w huv hvw, hwโฉ
  },
  { -- as before we prove by contradiction and forming a valuation that 
    -- falsifies the defining formula from the assumption that F is intransitive
    intros h4,
    refine โจ_โฉ,
    intros u v w huv hvw,
    by_contra,
    let V := ฮป _, {w}, -- so from world u, only โ โ p holds but not โ p since p 
                      -- is not true in v
    simp only [frame_eval, eval, not_forall, set.not_not_mem, exists_prop, 
               not_exists, not_and, forall_exists_index, and_imp] at h4,
    specialize h4 V u v huv w hvw (set.mem_singleton w),
    simp only [set.mem_singleton_iff, exists_eq_right] at h4,
    exact h h4
  }
end

/-- Euclidean frames are defined by formula 5 (again, historical reasons)-/
theorem ๐ฝ_euclidean_is_definable {p : vars} 
: defines (โ โฆpโฆ โน โก โ โฆpโฆ) ๐ฝ_euclidean :=
begin
  intro F,
  split,
  { simp only [frame_eval, eval, not_forall, set.not_not_mem, exists_prop, forall_exists_index, and_imp],
    rintros hF V u w huw hw v huv,
    use w,
    exact โจhF u v w huv huw, hwโฉ
  },
  { intros h5 u v w huv huw,
    by_contra,
    -- since ยฌ F.R v w, w is in this set so โ p holds in u by virtue of R u w.
    -- However, by construction โ p does not hold in v as p is false in all the 
    -- worlds accessible from v, so โก โ p does not hold in u. 
    let V := ฮป_, {z | ยฌ F.R v z},
    simp only [frame_eval, eval, not_forall, set.not_not_mem, exists_prop, 
               not_exists, not_and, forall_exists_index, and_imp] at h5,
    specialize h5 V u w huw h v huv,
    simp at h5,
    exact h5
  }
end

theorem ๐ฝ_inter {๐ฝโ ๐ฝโ : set frame} (h1 : defines A ๐ฝโ) (h2 : defines B ๐ฝโ)
: defines (A โ B) (๐ฝโ โฉ ๐ฝโ) :=
begin
  intro F,
  simp only [set.mem_inter_eq],
  rw [h1, h2],
  exact frame_eval_and F,
end

/-- The Lob formula characterise frames that are transitive and converse 
well-founded.-/
theorem ๐ฝ_transitive_converse_well_founded_is_definable {p : vars}
: defines (โก (โก โฆpโฆ โน โฆpโฆ) โน โก โฆpโฆ) (๐ฝ_transitive โฉ ๐ฝ_converse_well_founded)
:= begin
  intro F,
  split,
  { intros hF V w,
    rcases hF with โจhtrans, hwfโฉ,
    simp [๐ฝ_converse_well_founded, ๐ฝ] at hwf,
    -- Supppose for a contradiction that the defining formula is not true in F
    by_contra,
    -- So we have a world w s.t. w โฉ โก (โก p โน p) but w โฎ โก p
    unfold1 eval at h,
    simp only [not_forall, exists_prop] at h,
    rcases h with โจh1, h2โฉ,
    -- From this, we can form an infinite chain wโRwโ... of worlds to
    -- contradict R's (converse) wellfoundness.
    -- Since w โฎ โก p, w has an R-successor wโ s.t.  wโ โฎ p.
    -- Since w โฉ โก (โก p โน p). wโ โฉ โก p โน p. So by modus tolens, wโ โฎ โก p.
    -- Now we can repeat the argument: since wแตข โฎ โก p then wแตขโโ โฎ p for some
    -- successor wแตขโโ of wแตข. By transitivity, wแตขโโ is also a successor of w so
    -- wแตขโโ โฉ โก p โน p and hence we can conclude wแตขโโ โฎ โก p.

    -- To formalise this argument, we find a maximal world a satisfying the
    -- required conditions using the (converse) wellfoundness of R. We apply the
    -- inductive part of the argument to effectively show that since a = wแตข for
    -- some i, then a' = wแตขโโ is an R-successor of a, so in fact a is not the
    -- maximal world. This gives the required contradiction.
    haveI : is_trans F.W F.R := by { simp [๐ฝ_transitive, ๐ฝ] at htrans, exact htrans },
    -- the min of the flipped R is the max of R.
    obtain โจa, ha, hwfโฉ := 
      well_founded.has_min hwf 
      {u | F.R w u โง
        (โชF, Vโซ@@u โฉ โก โฆpโฆ โน โฆpโฆ) โง
        (โชF, Vโซ@@u โฎ (โก โฆpโฆ))} 
      -- the base case forms the proof of nonemptiness
      โจ_, _โฉ,
    rotate,

    -- The base case
    unfold1 eval at h2,
    simp only [not_forall, exists_prop] at h2,
    let wโ := classical.some h2,
    exact wโ,
    unfold1 eval at h2,
    simp only [not_forall, exists_prop] at h2,
    obtain โจhwwโ, h2โฉ := classical.some_spec h2,
    exact โจhwwโ, h1 _ hwwโ, mt (h1 _ hwwโ) h2โฉ,

    -- The inductive case 
    obtain โจhwa, ih1, ih2โฉ := ha,
    unfold1 eval at ih2, simp only [not_forall, exists_prop] at ih2,
    rcases ih2 with โจa', haa', ih2โฉ,
    have hwa' := trans hwa haa',
    specialize hwf a' โจhwa', h1 a' hwa', mt (h1 a' hwa') ih2โฉ,
    simp [inv_image, flip] at hwf,
    exact hwf haa',
  }, {
    sorry -- not enough time!
  }
end

/-- The first order frame language with one 2-ary relation symbol. -/
def L : first_order.language := {
  functions := ฮป _, empty,
  relations := ฮป n, match n with
    | 2 := unit
    | n := empty
  end
}

def realize_sentence' (M : L.Structure W) (S : L.sentence) 
:= realize_sentence W S

def first_order_definable (๐ฝ : set frame) (S : L.sentence) :=
begin
  refine โ F, F โ ๐ฝ โ _,
  let M : L.Structure F.W := {
    fun_map := ฮป n e args, empty.elim e, 
    rel_map := ฮป n t args, match n, args with
    | 2, args := F.R (args 0) (args 1)
    | n, args := false
    end
  },
  -- M โจ S
  exact realize_sentence' M S,
end

theorem ๐ฝ_reflexive_is_fodefinable : first_order_definable ๐ฝ_reflexive
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
  --            matrix.head_cons, ๐ฝ_reflexive, ๐ฝ, set.mem_set_of_eq],
  intro F,
  split,
  { intros hF, exact hF },
  { intros h, exact h }
end

/- The key reason for using this embedded first-order language is I wanted
to show that the converse-wellfounded + transitive class from before cannot
be defined by a first-order sentence. I never got around to it, but I still
learned about using lean's definitions for first-order logic.-/