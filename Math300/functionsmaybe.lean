import Math300.basic
import Mathlib

def Injective {X Y} (f : X → Y) : Prop :=
                         ∀ {x1 x2 : X}, f x1 = f x2 → x1 = x2
def Surjective {X Y} (f : X → Y) : Prop := ∀ y : Y, ∃ x : X, f x = y
def Bijective {X Y} (f : X → Y) : Prop := Injective f ∧ Surjective f
def Inverse {X Y} (f : X → Y) (g : Y → X) : Prop := g ∘ f = id ∧ f ∘ g = id

def f (x : ℝ) : ℝ := x^3 - x

example : ¬ Bijective f := by
  intro h
  have h_inj : Injective f := h.1
  have h1 : f 0 = f 1 := by
    simp [f]
  have h01 : (0 : ℝ) = 1 := h_inj h1
  norm_num at h01

example {X Y Z} {f : X → Y} {g : Y → Z}
    (hf : Bijective f) (hg : Bijective g) : Bijective (g ∘ f) := by
  constructor
  · -- injective
    intro x1 x2 h
    obtain ⟨hf_inj, hf_surj⟩ := hf
    obtain ⟨hg_inj, hg_surj⟩ := hg
    apply hf_inj
    apply hg_inj
    calc g (f x1) = (g ∘ f) x1 := by rfl
      _ = (g ∘ f) x2 := by rw [h]
      _ = g (f x2) := by rfl
  · -- surjective
    intro z
    obtain ⟨hf_inj, hf_surj⟩ := hf
    obtain ⟨hg_inj, hg_surj⟩ := hg
    obtain ⟨y, hy⟩ := hg_surj z
    obtain ⟨x, hx⟩ := hf_surj y
    use x
    calc (g ∘ f) x = g (f x) := by rfl
      _ = g y := by rw [hx]
      _ = z := by rw [hy]

example {X Y} {f : X → Y} {g : Y → X} (h : Inverse f g) : Inverse g f := by
  dsimp [Inverse]
  obtain ⟨hgf, hfg⟩ := h
  constructor
  · exact hfg
  · exact hgf

def f1 (z : ℤ × ℤ) : ℤ := z.1 - 2 * z.2 - 1

example : Surjective f1 ∧ ¬ Injective f1 := by
  constructor
  · intro z
    use (z + 1, 0)
    dsimp [f1]
    ring
  · intro h
    have h_eq : f1 (1, 0) = f1 (3, 1) := by
      dsimp [f1]
    have h_contra := h h_eq
    norm_num at h_contra

def fQ (p : ℚ × ℚ) : ℚ := p.1^2 - p.2^2

example : Surjective fQ := by
  intro q
  use ((q + 1) / 2, (q - 1) / 2)
  dsimp [fQ]
  ring
