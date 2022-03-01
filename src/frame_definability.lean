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

def L : first_order.language := {
  functions := λ _, empty,
  relations := λ n, match n with
    | 2 := unit
    | n := empty
  end
}

/-- Classes of models defined by a property of their frames. -/
def 𝔽 (F_prop : ∀ {W : Type}, (W → W → Prop) → Prop) : set frame :=
{F | F_prop F.R}

def 𝔽_reflexive : set frame :=
𝔽 (λ W R, ∀ w, R w w)

@[simp]
lemma 𝔽_reflexive_def (F : frame) : F ∈ 𝔽_reflexive ↔ ∀ w, F.R w w :=
by simp only [𝔽_reflexive, 𝔽, set.mem_set_of_eq] 

/-- A is true in a frame F iff M ⊩ A for every model M based on F. -/
def frame_eval (F : frame) (A : form vars) := ∀ V, ⟨F, V⟩ ⊩ A
notation F ` ⊩ ` A := frame_eval F A

/-- A is valid in a class of frames 𝔽 iff F ⊨ A for every frame F ∈ 𝔽. -/
def class_frame_valid (𝔽 : set frame) (A : form vars) := ∀ F ∈ 𝔽, F ⊩ A
notation 𝔽 ` ⊨ ` A := class_frame_valid 𝔽 A

def definable (𝔽 : set frame) (A : form vars) := 
∀ F, F ∈ 𝔽 ↔ (F ⊩ A)

theorem 𝔽_reflexive_is_definable {p : vars} 
: definable 𝔽_reflexive (⦃p⦄ ⟹ ◇⦃p⦄) := 
begin
  intro F,
  simp only [𝔽_reflexive_def, diamond_eq_not_box_not],
  split,
  { intros hF V w, 
    simp only [eval, not_forall, set.not_not_mem, exists_prop],
    intro hw,
    use w,
    exact ⟨hF w, hw⟩ },
  { sorry }
end

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
  -- simp only [first_order_definable, realize_sentence', realize_sentence,
  --            formula.realize, realize_all, realize_rel, term.realize,
  --            matrix.cons_val_zero, sum.elim_inr, matrix.cons_val_one, 
  --            matrix.head_cons, 𝔽_reflexive, 𝔽, set.mem_set_of_eq],
  intro F,
  split,
  { intros hF M, apply hF },
  { intros h w, exact h w }
end
