import E2.ExactSourceModel
import E2.ExactInitializationAlgebra

namespace E2.ExactForcing
noncomputable section
open ExactClock
variable {A : Type*} [CStarAlgebra A]

def shiftHom (t : A) (ht : star t*t=1 ∧ t*star t=1) (j : ℕ) : A →⋆ₐ[ℂ] A where
  toFun a := ctranslate t a j
  map_zero' := by simp [ctranslate]
  map_add' a b := by simp [ctranslate,mul_add,add_mul]
  map_one' := shift_one t ht j
  map_mul' a b := shift_mul t a b ht j
  commutes' r := by simp [Algebra.algebraMap_eq_smul_one,shift_smul,shift_one t ht j]
  map_star' a := (shift_star t a j).symm

def decodeWord (σ : A →⋆ₐ[ℂ] A) (a b : A) (n : ℕ) : A :=
  ((List.range n).map (fun j => (σ^[j]) a)).prod * (σ^[n]) b

theorem decodeWord_zero (σ : A →⋆ₐ[ℂ] A) (a b : A) : decodeWord σ a b 0=b := by
  simp [decodeWord]

theorem decodeWord_succ (σ : A →⋆ₐ[ℂ] A) (a b : A) (n : ℕ) :
    decodeWord σ a b (n+1)=a*σ (decodeWord σ a b n) := by
  simp only [decodeWord,List.prod_range_succ',Function.iterate_zero,Function.id_def,
    map_mul,Function.iterate_succ_apply',←mul_assoc]
  congr 1
  simp only [map_list_prod,List.map_map,Function.comp_def]

theorem decodeWord_commute (σ : A →⋆ₐ[ℂ] A) (a b z : A) (n : ℕ)
    (ha : ∀ j, Commute ((σ^[j]) a) z) (hb : Commute ((σ^[n]) b) z) :
    Commute (decodeWord σ a b n) z := by
  apply Commute.mul_left _ hb
  apply Commute.list_prod_left
  intro x hx
  obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hx
  exact ha j

theorem model_digit_commute (m : ExactModel clockPresentation A) (i j : ℕ) :
    Commute (ctranslate (m.value 2) (m.value 1) i) (ctranslate (m.value 2) (m.value 1) j) := by
  rw [(model_digits m).2.1 i,(model_digits m).2.1 j]
  exact cfc_commute_cfc _ _ _

theorem commute_star_unitary (u z : A) (hu : star u*u=1 ∧ u*star u=1)
    (h : Commute u z) : Commute (star u) z := by
  change star u*z=z*star u
  calc
    star u*z = star u*z*(u*star u) := by rw [hu.2,mul_one]
    _ = star u*(z*u)*star u := by simp only [mul_assoc]
    _ = star u*(u*z)*star u := by rw [h.eq]
    _ = z*star u := by rw [←mul_assoc,hu.1,one_mul]

theorem commute_shift (t x z : A) (j : ℕ) (ht : star t*t=1 ∧ t*star t=1)
    (htz : Commute t z) (hxz : Commute x z) : Commute (ctranslate t x j) z :=
  ((htz.pow_left j).mul_left hxz).mul_left ((commute_star_unitary t z ht htz).pow_left j)

theorem shiftHom_iterate (t : A) (ht : star t*t=1 ∧ t*star t=1) (s n : ℕ) (x : A) :
    ((shiftHom t ht s)^[n]) x=ctranslate t x (s*n) := by
  induction n with
  | zero => simp [shift_zero]
  | succ n ih =>
    rw [Function.iterate_succ_apply',ih]
    change ctranslate t (ctranslate t x (s*n)) s=_
    rw [shift_shift,Nat.mul_succ]

theorem shift_projection (t x : A) (ht : star t*t=1 ∧ t*star t=1)
    (hx : x*x=x) (j : ℕ) : ctranslate t x j*ctranslate t x j=ctranslate t x j := by
  rw [←shift_mul t x x ht j,hx]

theorem source_cross {p : CounterProgram} (m : ExactModel (sourcePresentation p) A)
    (c e : Fin 3) (hce : c<e) (i j : Fin 4) :
    Commute (sourceValue m (4*c.val+i.val)) (sourceValue m (4*e.val+j.val)) := by
  have h := m.equations _ (source_clock_cross_relation p c e hce i j)
  exact sub_eq_zero.mp (by simpa only [pc,Poly.evalC_sub,Poly.evalC_mul,sv,Poly.evalC_var,sourceValue] using h)

theorem source_initial_relations {p : CounterProgram} (m : ExactModel (sourcePresentation p) A) :
    let v := sourceValue m
    let a := (1-v 1)*(1-ctranslate (v 2) (v 1) 1)
    let b := v 1*(1-ctranslate (v 2) (v 1) 1)
    v 15=b+a*ctranslate (v 2) (v 15) 2 ∧
    v 16=(1-a)+(1/2:ℂ) • (a*ctranslate (v 2) (v 16) 2) ∧
    v 17=(1-v 5)+v 5*(1-v 9)*ctranslate (v 6*v 10) (v 17) 1 := by
  let v := sv p
  let a := (1-v 1)*(1-conjP (v 2) (v 1))
  let b := v 1*(1-conjP (v 2) (v 1))
  let H := b+a*conjP (v 2^2) (v 15)
  let L := (1-a)+.const (1/2)*a*conjP (v 2^2) (v 16)
  let Z := (1-v 5)+v 5*(1-v 9)*conjP (v 6*v 10) (v 17)
  have hmem (r : SourcePoly p) (hr : r ∈ [v 15-H,v 16-L,v 17-Z]) :
      r ∈ (sourcePresentation p).relations := by
    simp only [sourcePresentation,sourceRelations,Id.run,pure,List.append_assoc,List.mem_append]
    iterate 6 apply Or.inr
    apply Or.inl
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl | rfl <;> simp only [v,a,b,H,L,Z,List.mem_cons,List.not_mem_nil,or_false] <;> tauto
  have heval (x y : SourcePoly p) (h : x-y ∈ (sourcePresentation p).relations) :
      x.evalC m.value=y.evalC m.value := sub_eq_zero.mp (by simpa only [Poly.evalC_sub] using m.equations _ h)
  have hpw : Poly.evalC m.value (v 2^2) = sourceValue m 2^2 := by
    have hw : (v 2^2)=v 2*(v 2*1) := rfl
    rw [hw,Poly.evalC_mul,Poly.evalC_mul,Poly.evalC_one]
    simp [v,sv,sourceValue,pow_two]
  refine ⟨?_,?_,?_⟩
  · have h := heval (v 15) H (hmem _ (by simp))
    dsimp only [H,a,b,conjP] at h
    simp only [Poly.evalC_add,Poly.evalC_sub,Poly.evalC_mul,Poly.evalC_adj,hpw] at h
    simpa only [v,conjP,Poly.evalC_mul,Poly.evalC_add,Poly.evalC_sub,Poly.evalC_adj,
      Poly.evalC_one,hpw,sv,Poly.evalC_var,sourceValue,ctranslate,pow_one,star_pow] using h
  · have h := heval (v 16) L (hmem _ (by simp))
    dsimp only [L,a,conjP] at h
    simp only [Poly.evalC_add,Poly.evalC_sub,Poly.evalC_mul,Poly.evalC_adj,hpw] at h
    simpa only [v,conjP,Poly.evalC_mul,Poly.evalC_add,Poly.evalC_sub,Poly.evalC_adj,
      Poly.evalC_one,Poly.evalC_const,hpw,sv,Poly.evalC_var,sourceValue,ctranslate,pow_one,star_pow,
      smul_mul_assoc,one_mul,mul_smul_comm,mul_assoc,Rat.cast_div,Rat.cast_one,Rat.cast_ofNat] using h
  · have h := heval (v 17) Z (hmem _ (by simp))
    simpa only [Z,v,conjP,Poly.evalC_mul,Poly.evalC_add,Poly.evalC_sub,Poly.evalC_adj,
      Poly.evalC_one,sv,Poly.evalC_var,sourceValue,ctranslate,pow_one] using h

theorem address_initialization {p : CounterProgram} (m : ExactModel (sourcePresentation p) A) :
    (∀ e, addressCylinder m e*sourceValue m 15=addressCylinder m e) ∧
    (∀ e, addressCylinder m e*sourceValue m 16=((2:ℂ)^(-(e:ℤ))) • addressCylinder m e) := by
  let v := sourceValue m
  let t := v 2
  let P := ctranslate t (v 1)
  let a := (1-v 1)*(1-P 1)
  let b := v 1*(1-P 1)
  have ht : star t*t=1 ∧ t*star t=1 := (sourceClockModel m 0).domains 2
  let σ := shiftHom t ht 2
  have hp0 : IsIdempotentElem (v 1) := ((sourceClockModel m 0).domains 1).2
  have hp : ∀ j, IsIdempotentElem (P j) := shift_projection _ _ ht hp0
  have hpp (i j : ℕ) : Commute (P i) (P j) := model_digit_commute (sourceClockModel m 0) i j
  have h0 : P 0=v 1 := shift_zero _ _
  have hpc (i j : ℕ) : Commute (P i) (1-P j) := (Commute.one_right _).sub_right (hpp i j)
  have hcc (i j : ℕ) : Commute (1-P i) (1-P j) :=
    (Commute.one_left _).sub_left (hpc i j)
  have haa : a*a=a := by
    change IsIdempotentElem ((1-v 1)*(1-P 1))
    rw [←h0]
    exact IsIdempotentElem.mul_of_commute (hcc 0 1) (hp 0).one_sub (hp 1).one_sub
  have hbb : b*b=b := by
    change IsIdempotentElem (v 1*(1-P 1))
    rw [←h0]
    exact IsIdempotentElem.mul_of_commute (hpc 0 1) (hp 0) (hp 1).one_sub
  have hab : a*b=0 := by
    change (1-v 1)*(1-P 1)*(v 1*(1-P 1))=0
    rw [←h0,(hpc 0 1).symm.mul_mul_mul_comm,(hp 0).one_sub_mul_self,zero_mul]
  have hba : b*a=0 := by
    change v 1*(1-P 1)*((1-v 1)*(1-P 1))=0
    rw [←h0,(hcc 1 0).mul_mul_mul_comm,(hp 0).mul_one_sub_self,zero_mul]
  have hea (n : ℕ) : Commute (decodeWord σ a b n) a := by
    apply decodeWord_commute
    · intro j
      change Commute (((shiftHom t ht 2)^[j]) a) a
      rw [shiftHom_iterate]
      dsimp only [a]
      rw [shift_mul t _ _ ht,shift_sub,shift_sub,shift_one t ht,shift_shift]
      change Commute ((1-P (2*j))*(1-P (1+2*j))) ((1-v 1)*(1-P 1))
      rw [←h0]
      exact ((hcc _ _).mul_right (hcc _ _)).mul_left ((hcc _ _).mul_right (hcc _ _))
    · change Commute (((shiftHom t ht 2)^[n]) b) a
      rw [shiftHom_iterate]
      dsimp only [a,b]
      rw [shift_mul t _ _ ht,shift_sub,shift_one t ht,shift_shift]
      change Commute (P (2*n)*(1-P (1+2*n))) ((1-v 1)*(1-P 1))
      rw [←h0]
      exact ((hpc _ _).mul_right (hpc _ _)).mul_left ((hcc _ _).mul_right (hcc _ _))
  have hE (n : ℕ) : decodeWord σ a b n=addressCylinder m n := by
    simp only [decodeWord,σ,shiftHom_iterate]
    rfl
  have hrels := source_initial_relations m
  have hH : v 15=b+a*σ (v 15) := hrels.1
  have hL : v 16=(1-a)+(1/2:ℂ) • (a*σ (v 16)) := hrels.2.1
  have h := address_decode σ a b (v 15) (v 16) (1/2) (decodeWord σ a b)
    haa hbb hab hba (decodeWord_zero _ _ _) (decodeWord_succ _ _ _)
    (fun n => (hea n).eq) hH hL
  constructor
  · intro e
    simpa only [hE] using (h e).1
  · intro e
    have hc : (1/2:ℂ)^e=(2:ℂ)^(-(e:ℤ)) := by simp [zpow_neg,one_div,inv_pow]
    simpa only [hE,hc] using (h e).2

end
end E2.ExactForcing
