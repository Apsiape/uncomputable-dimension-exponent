import E2.ExactFlagDensity
import Mathlib.Analysis.CStarAlgebra.lpSpace

namespace E2.ExactCompactness
noncomputable section
open scoped ENNReal Pointwise
set_option linter.unusedSimpArgs false
variable {A : Type*} [CStarAlgebra A]

theorem spectrum_one_sub (x : A) :
    spectrum ℝ (1-x)=({1}:Set ℝ)-spectrum ℝ x := by
  simpa only [map_one] using (spectrum.singleton_sub_eq x (1:ℝ)).symm

theorem positive_complement (x : A) (hx : Domain.positiveContraction.HoldsC x) :
    Domain.positiveContraction.HoldsC (1-x) := by
  refine ⟨(IsSelfAdjoint.one _).sub hx.1,?_⟩
  rw [spectrum_one_sub]
  intro r hr
  obtain ⟨a,ha,b,hb,hab⟩ := Set.mem_sub.mp hr
  have ha1 : a=1 := Set.mem_singleton_iff.mp ha
  subst a
  obtain ⟨hb0,hb1⟩ := hx.2 hb
  constructor <;> linarith

theorem positive_of_norms (x : A) (hx : IsSelfAdjoint x) (hn : ‖x‖≤1) (hc : ‖1-x‖≤1) :
    Domain.positiveContraction.HoldsC x := by
  refine ⟨hx,?_⟩
  intro r hr
  have hrn := (quasispectrum.norm_le_norm_of_mem (spectrum_subset_quasispectrum ℝ x hr)).trans hn
  have hs : 1-r ∈ spectrum ℝ (1-x) := by
    rw [spectrum_one_sub]
    exact Set.sub_mem_sub (Set.mem_singleton 1) hr
  have hsn := (quasispectrum.norm_le_norm_of_mem (spectrum_subset_quasispectrum ℝ (1-x) hs)).trans hc
  constructor <;> nlinarith [Real.le_norm_self r,Real.le_norm_self (1-r)]

variable {I : Type*} {B : I → Type*} [∀ i, CStarAlgebra (B i)] [∀ i, Nontrivial (B i)]

abbrev BoundedProduct (B : I → Type*) [∀ i, CStarAlgebra (B i)] := lp B ∞

instance boundedProductCStar : CStarAlgebra (BoundedProduct B) where

def coordinate (i : I) : BoundedProduct B →⋆ₐ[ℂ] B i where
  toFun a := a i
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  commutes' _ := rfl
  map_star' _ := rfl

theorem product_domain (d : Domain) (a : BoundedProduct B) (ha : ∀ i, d.HoldsC (a i)) :
    d.HoldsC a := by
  cases d with
  | positiveContraction =>
    apply positive_of_norms
    · change star a=a
      apply lp.ext
      funext i
      exact (ha i).1
    · apply lp.norm_le_of_forall_le (by norm_num)
      exact fun i => ExactForcing.contraction_norm _ (ha i).1 (ha i).2
    · apply lp.norm_le_of_forall_le (by norm_num)
      intro i
      have hc := positive_complement (a i) (ha i)
      exact ExactForcing.contraction_norm _ hc.1 hc.2
  | projection =>
    constructor
    · apply lp.ext; funext i; exact (ha i).1
    · apply lp.ext; funext i; exact (ha i).2
  | unitary =>
    constructor
    · apply lp.ext; funext i; exact (ha i).1
    · apply lp.ext; funext i; exact (ha i).2
  | reflection =>
    constructor
    · apply lp.ext; funext i; exact (ha i).1
    · apply lp.ext; funext i; exact (ha i).2

theorem coordinate_polynomial {ι : Type*} (x : ι → BoundedProduct B) (r : Poly ι) (i : I) :
    (r.evalC x) i=r.evalC (fun j => x j i) := by
  exact (ExactTrace.eval_map (coordinate i) x r).symm

def boundedTuple {ι : Type*} (x : ∀ i, ι → B i) (hx : ∀ i j, ‖x i j‖≤1) (j : ι) :
    BoundedProduct B := ⟨fun i => x i j,memℓp_infty ⟨1,by rintro y ⟨i,rfl⟩; exact hx i j⟩⟩

theorem boundedTuple_domain {ι : Type*} (d : ι → Domain) (x : ∀ i, ι → B i)
    (hx : ∀ i j, ‖x i j‖≤1) (hd : ∀ i j, (d j).HoldsC (x i j)) (j : ι) :
    (d j).HoldsC (boundedTuple x hx j) := product_domain _ _ (fun i => hd i j)

end
end E2.ExactCompactness
