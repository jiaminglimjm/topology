import tactic

open set

#print sUnion

structure topology :=
(X : Type)
(τ : set (set X))
(has_univ : univ ∈ τ)
(has_sUnion : ∀ S ⊆ τ, ⋃₀ S ∈ τ)
(has_inter : ∀ U₁ U₂ ∈ τ, U₁ ∩ U₂ ∈ τ)

namespace topology

#check {(∅:set ℕ), (univ:set ℕ)}

lemma barton  : ∀ s : set ℚ,  s ∈ ({∅, univ} : set (set ℚ)) ↔ ∃ p, ∀ x, (x ∈ s) ↔ p :=
begin
  intro s,
  split,
    intro h,
    cases h,
    use false,
    intro x, rw h, simp,
    use true,
    intro x,
    simp at h,
    simp [h],
  intro h,
  cases h with p hp,
  by_cases p,
    right,
    simp,
    ext x,
    specialize hp x,
    finish,
  left,
  ext x,
  specialize hp x,
  split,
    intro hxs,
    exact h (hp.1 hxs),
  intro f,
  exfalso, exact f,
end.

def trivial_topology : topology :=
{ X := ℚ,
  τ := {∅, univ},
  has_univ := by simp,
  has_sUnion := begin
    intros S hS,

    rw barton,
    by_cases hh : univ ∈ S,
    use true,
    intro x,
    split,
      intro h,
      dsimp at h,
      rcases h with ⟨q, hq, hxq⟩,
      specialize hS hq,
      cases hS,
      finish, finish,
    intro h,
    simp,
    use univ,
    split, simp [hh], trivial,


    use false,
    intro x,
    split,
      intro h,
      dsimp at h,
      rcases h with ⟨q, hq, hxq⟩,
      apply hh,
      specialize hS hq,
      cases hS,
      rw hS at hxq,
      exfalso, exact hxq,

    simp at hS,
    rw ←hS,
    exact hq,
    intro hf, exfalso, exact hf,
    /-
    by_cases h₁ : S = ∅, simp * at *,
    by_cases h₂ : S = {∅}, simp * at *,
    by_cases h₃ : S = {univ}, simp * at *,
    by_cases h₄ : S = {∅, univ}, simp * at *,
    exfalso,
    finish-/
    sorry,
    end,
  has_inter := by finish }

end topology


namespace topology

def discrete_topology : topology :=
⟨Sort*, univ, by simp, by simp, by simp⟩


example : X = X := rfl

--lemma has_empty : (∅ : set ℕ) ∈ discrete_topology.τ := trivial

#check has_univ

variable {T : topology}

example : ∅ ∈ T.τ :=
begin
  have : ⋃₀ ∅ ∈ T.τ,
    apply has_sUnion,
    intro x,
    intro h,
    exfalso,
    exact h,
  simpa using this,
end

structure basis :=
(X : Sort*)
(𝒷 : set (set X))
(all_in_some : ∀ x, ∃ B ∈ 𝒷, x ∈ B)
(some_subset_inter : ∀ x B₁ B₂, x ∈ B₁ → x ∈ B₂ → ∃ B₃ ∈ 𝒷, x ∈ B₃ ∧ B₃ ⊆ B₁ ∩ B₂)

def b : set (set ℕ) := {{0}, {1, 2}}
def K := {s | ∃ S ⊆ b, ⋃₀ S = s }

example : {0,1,2} ∈ K :=
begin
  dsimp [K],
  use {{0}, {1, 2}},
  split,
    unfold b, simp,
end

/-
example (B : basis) : topology :=
begin
  rcases B with ⟨X, 𝒷, h₁, h₂⟩,
  fconstructor,
  use X,
  use {s | ∃ S ⊆ 𝒷,  ⋃₀ S = s },
  use 𝒷, use rfl.subset, ext x, sorry,
{ intros S hS,
  apply hS,
  sorry,
  /-
  use S,
  split,
    intros U hU,
    specialize hS hU, dsimp at hS,
    rcases hS with ⟨S', hS'b, hUS'⟩,
    sorry, refl,-/ },

  rintros U₁ U₂ ⟨S₁, hS₁, hU₁⟩ ⟨S₂, hS₂, hU₂⟩, dsimp at *,

  use {s | s ∈ S₁ ∩ S₂},
  split,
    intros U hU, dsimp at hU,
    exact hS₁ hU.1,

  ext x,
  split,
    intro h,
    dsimp at h,
    rcases h with ⟨B, ⟨hB₁, hB₂⟩, hxB⟩,
    split,
      rw ← hU₁,
      dsimp,
      use B,
      use hB₁,
      use hxB,
    rw ← hU₂,
    use B,
    use hB₂,
    use hxB,

  rintro ⟨hl, hr⟩,
  simp [←hU₁, ←hU₂] at hl hr,
  cases hl with B₁ hB₁,
  cases hr with B₂ hB₂,

  rcases h₂ x B₁ B₂ hB₁.2 hB₂.2 with ⟨B₃, hB₃,h⟩,
  dsimp, -- needs Choice here?

  use B₃,
  split,
    split,
    have := h.2 h.1,
    rcases h₁ x with ⟨B₄, hB₄, hh⟩,
  sorry,

  /-
  use S₁ ∪ S₂, split,  apply  union_subset, assumption, assumption,
  rw sUnion_union, rw hU₁, rw hU₂,
  ext x,
  split,
    rintro (h | h),
    use h,

    rw ←hU₂,
    simp,
    rcases h₁ x with ⟨P, hP, hh⟩,
    use P,
  sorry,
  sorry,
  rintro ⟨hl, hr⟩,
  left, assumption,
-/

end
-/

def generate (B : basis) : topology :=
begin
  rcases B with ⟨X, 𝒷, h₁, h₂⟩,
  fconstructor,

  use X,

  use { U | ∀ x ∈ U, ∃ B ∈ 𝒷, x ∈ B ∧ B ⊆ U },

  intros x hx,
  rcases h₁ x with ⟨B, hB, hxB⟩,
  use B,
  use hB,
  use hxB,
  intros b hb, trivial,

  intros S hS,
  simp at *,
  intros x U hUS hxU,
  specialize hS hUS x hxU,
  rcases hS with ⟨B, hB𝒷, hxB, hBU⟩,
  use B, use hB𝒷, use hxB,
  intros b hbB,
  dsimp,
  use U,
  use hUS,
  apply hBU,
  use hbB,

  intros U₁ U₂ hU₁ hU₂,
  dsimp at *,
  rintro x ⟨hx₁, hx₂⟩,
  rcases hU₁ x hx₁ with ⟨B₁, hB₁, hxB₁, hBU₁⟩,
  rcases hU₂ x hx₂ with ⟨B₂, hB₂, hxB₂, hBU₂⟩,
  rcases h₂ x B₁ B₂ hxB₁ hxB₂ with ⟨B₃, hB₃, hxB₃, hBU₃⟩,
  use B₃,
  use hB₃,
  use hxB₃,
  refine subset.trans hBU₃ _,
  intros b hb,
  use hBU₁ hb.1,
  use hBU₂ hb.2,
end

example (B : basis) : (generate B).X = B.X := begin
  unfold generate,
  sorry,
end

-- Type class problems?
example (B : basis) : (generate B).τ = {s | ∃ S ⊆ B.𝒷,  ⋃₀ S = s } :=
begin
  sorry
end

example (T : topology) : basis :=
begin
rcases T with ⟨X, τ, h₁, h₂, h₃⟩,
fconstructor,

use X,

use { U | U ∈ τ ∧ ∀ x ∈ U, ∃ C, x ∈ C ∧ C ⊆ U },

intro x, sorry,

sorry,

end


end topology







class topological_space (X : Type) :=
(is_open : set X → Prop)
(is_open_univ : is_open univ)
(is_open_sUnion : ∀ 𝒞 : set (set X), (∀ U ∈ 𝒞, is_open U) → is_open (⋃₀ 𝒞))
(is_open_inter : ∀ U₁ U₂, is_open U₁ → is_open U₂ → is_open (U₁ ∩ U₂))

namespace topological_space

variables (X : Type) [topological_space X]

@[simp] lemma is_open_univ' : is_open (univ : set X) :=
is_open_univ
@[simp] lemma is_open_inter' :
  ∀ U₁ U₂ : set X, is_open U₁ → is_open U₂ → is_open (U₁ ∩ U₂) :=
is_open_inter
@[simp] lemma is_open_sUnion' :
  ∀ 𝒞 : set (set X), (∀ U ∈ 𝒞, is_open U) → is_open (⋃₀ 𝒞) :=
is_open_sUnion

lemma is_open_empty : is_open (∅ : set X) :=
begin
  have : is_open (⋃₀ ∅) :=
    is_open_sUnion (∅ : set (set X)) (λ x (h : x ∈ ∅), by cases h),
  rwa ←sUnion_empty,
end

lemma is_open_Union {ι : Type} {f : ι → set X} (h : ∀ i : ι, is_open (f i)) :
  is_open (⋃ i, f i) :=
is_open_sUnion _ (λ U ⟨i, hi⟩, hi ▸ (h i))

lemma is_open_sInter {𝒞 : set (set X)} (h𝒞 : finite 𝒞) :
  (∀ U ∈ 𝒞, is_open U) → is_open (⋂₀ 𝒞) :=
begin
  apply finite.induction_on h𝒞,
    intro _,
    rw sInter_empty,
    exact is_open_univ,
  intros,
  sorry --show_term {finish},
end.




end topological_space
