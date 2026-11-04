import E2.ExactInitializationModel

namespace E2.ExactForcing
noncomputable section
open ExactClock
variable {A : Type*} [CStarAlgebra A]

theorem unitary_mul (t u : A) (ht : star t*t=1 ∧ t*star t=1)
    (hu : star u*u=1 ∧ u*star u=1) :
    star (t*u)*(t*u)=1 ∧ (t*u)*star (t*u)=1 := by
  constructor <;> simp only [star_mul,mul_assoc,←mul_assoc (star t) t,
    ←mul_assoc u (star u),ht.1,hu.2,one_mul,ht.2,hu.1]

theorem shift_mul_fixed (t u x : A) (hu : star u*u=1 ∧ u*star u=1)
    (hux : Commute u x) : ctranslate (t*u) x 1=ctranslate t x 1 := by
  simp only [ctranslate,pow_one,star_mul]
  calc
    (t*u)*x*(star u*star t) = t*(u*x*star u)*star t := by simp only [mul_assoc]
    _ = t*x*star t := by rw [hux.eq,mul_assoc x u,hu.2,mul_one]

theorem reset_initialization {p : CounterProgram} (m : ExactModel (sourcePresentation p) A) :
    ∀ k, fuelCylinder m k*sourceValue m 17=fuelCylinder m k*timeZeroCylinder m k := by
  let v := sourceValue m
  let t := v 6
  let u := v 10
  let P := ctranslate t (v 5)
  let Q := ctranslate u (v 9)
  have ht : star t*t=1 ∧ t*star t=1 := (sourceClockModel m 1).domains 2
  have hu : star u*u=1 ∧ u*star u=1 := (sourceClockModel m 2).domains 2
  have htu : Commute t u := source_cross m 1 2 (by decide) 2 2
  have hup : Commute u (v 5) := (source_cross m 1 2 (by decide) 1 2).symm
  have htq : Commute t (v 9) := source_cross m 1 2 (by decide) 2 1
  have hpq : Commute (v 5) (v 9) := source_cross m 1 2 (by decide) 1 1
  have hp0 : IsIdempotentElem (v 5) := ((sourceClockModel m 1).domains 1).2
  let σ := shiftHom (t*u) (unitary_mul t u ht hu) 1
  have hsP (j : ℕ) : σ (P j)=P (j+1) := by
    change ctranslate (t*u) (P j) 1=_
    rw [shift_mul_fixed t u _ hu (commute_shift t (v 5) u j ht htu hup.symm).symm]
    exact shift_shift t (v 5) j 1
  have hsQ (j : ℕ) : σ (Q j)=Q (j+1) := by
    change ctranslate (t*u) (Q j) 1=_
    rw [htu.eq,shift_mul_fixed u t _ ht (commute_shift u (v 9) t j hu htu.symm htq.symm).symm]
    exact shift_shift u (v 9) j 1
  have hiP (j : ℕ) : (σ^[j]) (v 5)=P j := by
    induction j with
    | zero => exact (shift_zero _ _).symm
    | succ j ih => rw [Function.iterate_succ_apply',ih,hsP]
  have hiQ (j : ℕ) : (σ^[j]) (1-v 9)=1-Q j := by
    induction j with
    | zero => simp [Q,shift_zero]
    | succ j ih => rw [Function.iterate_succ_apply',ih,map_sub,map_one,hsQ]
  have hiN (j : ℕ) : (σ^[j]) (1-v 5)=1-P j := by
    induction j with
    | zero => simp [P,shift_zero]
    | succ j ih => rw [Function.iterate_succ_apply',ih,map_sub,map_one,hsP]
  have hi1 (j : ℕ) : (σ^[j]) (1:A)=1 := by
    induction j with
    | zero => rfl
    | succ j ih => rw [Function.iterate_succ_apply',ih,map_one]
  let F := decodeWord σ (v 5) (1-v 5)
  let T := decodeWord σ (1-v 9) 1
  have hF (j : ℕ) : F j=fuelCylinder m j := by
    simp only [F,decodeWord,hiP,hiN]
    rfl
  have hT (j : ℕ) : T j=timeZeroCylinder m j := by
    simp only [T,decodeWord,hiQ,hi1,mul_one]
    rfl
  have hFp (j : ℕ) : Commute (F j) (v 5) := by
    apply decodeWord_commute
    · intro i
      rw [hiP,←shift_zero t (v 5)]
      exact model_digit_commute (sourceClockModel m 1) i 0
    · rw [hiN]
      exact (Commute.one_left _).sub_left (by
        rw [←shift_zero t (v 5)]
        exact model_digit_commute (sourceClockModel m 1) j 0)
  have hFq (j : ℕ) : Commute (F j) (1-v 9) := by
    apply (Commute.one_right _).sub_right
    apply decodeWord_commute
    · intro i
      rw [hiP]
      exact commute_shift t (v 5) (v 9) i ht htq hpq
    · rw [hiN]
      exact (Commute.one_left _).sub_left (commute_shift t (v 5) (v 9) j ht htq hpq)
  have hFs (j : ℕ) : F (j+1)=v 5*σ (F j) := decodeWord_succ _ _ _ _
  have hTs (j : ℕ) : T (j+1)=(1-v 9)*σ (T j) := decodeWord_succ _ _ _ _
  have hFpp (j : ℕ) : F (j+1)*v 5=F (j+1) := by
    rw [(hFp _).eq,hFs,←mul_assoc,hp0.eq]
  have hZ : v 17=(1-v 5)+v 5*(1-v 9)*σ (v 17) := (source_initial_relations m).2.2
  have h := reset_decode σ (v 5) (1-v 9) (v 17) F T hp0
    (decodeWord_zero _ _ _) (decodeWord_zero _ _ _) hFs hTs hFpp
    (fun j => (hFq (j+1)).eq) hZ
  intro k
  simpa only [hF,hT] using h k

end
end E2.ExactForcing
