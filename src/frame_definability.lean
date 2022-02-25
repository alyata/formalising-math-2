import formula
import semantics
import schemas_classes

variables {vars : Type} [denumerable vars] {W : Type} [nonempty W]
variables {A B C : form vars}

/-- A is valid in frame F iff M ⊩ A for every model M based on F. -/
def frame_valid (F : frame W) (A : form vars) := ∀ V, ⟨F, V⟩ ⊩ A
notation F ` ⊨ ` A := frame_valid F A

/-- A is valid in a class of frames 𝔽 iff F ⊨ A for every frame F ∈ 𝔽. -/
def class_frame_valid (𝔽 : set (frame W)) (A : form vars) := ∀ F ∈ 𝔽, F ⊨ A
notation 𝔽 ` ⊨ ` A := class_frame_valid 𝔽 A

