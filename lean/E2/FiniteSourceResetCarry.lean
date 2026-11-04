import E2.FiniteSourceDiagonal

namespace E2.FiniteConstruction
noncomputable section
open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator

theorem listReset_real_rotation (q t : Bool) (qs ts : List Bool) (h : qs.length=ts.length) :
    boolValue (listReset (q::qs) (t::ts)) = (1-boolValue q)+
      boolValue q*(1-boolValue t)*
        boolValue (listReset (listRotate (q::qs)) (listRotate (t::ts))) := by
  rw [listReset_rotation q t qs ts h]
  cases q <;> cases t <;> norm_num [boolValue]

theorem source_carry_recursion_matrix (p : CounterProgram) (N : ℕ) (hN : 0<N) :
    sourceCore p N 14=(1-sourceCore p N 1)+
      (1/4:ℂ) • (sourceCore p N 1*(sourceCore p N 2*sourceCore p N 14*(sourceCore p N 2).conjTranspose)) := by
  let k := finiteSlots p N
  change sourceDiagonal N k (fun z => listCarry z.1.1.val)=
    (1-sourceDiagonal N k (fun z => boolValue (z.1.1.val.headD false)))+
      (1/4:ℂ) • (sourceDiagonal N k (fun z => boolValue (z.1.1.val.headD false))*
        ((sourcePerm N k (addressLift (addressRotation p N k))).permMatrix ℂ*
          sourceDiagonal N k (fun z => listCarry z.1.1.val)*
          ((sourcePerm N k (addressLift (addressRotation p N k))).permMatrix ℂ).conjTranspose))
  rw [sourceConj_diagonal,sourceDiagonal_one_sub,sourceDiagonal_mul]
  rw [show (1/4:ℂ)=(((1/4:ℝ):ℝ):ℂ) by norm_num,sourceDiagonal_real_smul,sourceDiagonal_add]
  congr 1
  funext z
  have hread : (addressLift (addressRotation p N k) z).1.1=rotateBinary N z.1.1 := rfl
  rw [hread]
  have hlen := z.1.1.property
  change listCarry z.1.1.val=(1-boolValue (z.1.1.val.headD false))+
    (1/4:ℝ)*(boolValue (z.1.1.val.headD false)*listCarry (listRotate z.1.1.val))
  cases hb : z.1.1.val with
  | nil => simp only [hb,List.length_nil] at hlen; omega
  | cons b bs => simpa only [List.headD_cons,mul_assoc] using listCarry_rotation b bs

theorem source_reset_recursion_matrix (p : CounterProgram) (N : ℕ) (hN : 0<N) :
    sourceCore p N 17=(1-sourceCore p N 5)+sourceCore p N 5*(1-sourceCore p N 9)*
      (sourceCore p N 6*(sourceCore p N 10*sourceCore p N 17*(sourceCore p N 10).conjTranspose)*
        (sourceCore p N 6).conjTranspose) := by
  let k := finiteSlots p N
  change sourceDiagonal N k (fun z => boolValue (listReset z.2.1.val z.2.2.val))=
    (1-sourceDiagonal N k (fun z => boolValue (z.2.1.val.headD false)))+
      sourceDiagonal N k (fun z => boolValue (z.2.1.val.headD false))*
        (1-sourceDiagonal N k (fun z => boolValue (z.2.2.val.headD false)))*
      ((sourcePerm N k (fuelLift (rotateBinary N))).permMatrix ℂ*
        ((sourcePerm N k (timeLift (rotateBinary N))).permMatrix ℂ*
          sourceDiagonal N k (fun z => boolValue (listReset z.2.1.val z.2.2.val))*
          ((sourcePerm N k (timeLift (rotateBinary N))).permMatrix ℂ).conjTranspose)*
        ((sourcePerm N k (fuelLift (rotateBinary N))).permMatrix ℂ).conjTranspose)
  rw [sourceConj_diagonal,sourceConj_diagonal,sourceDiagonal_one_sub,sourceDiagonal_one_sub,
    sourceDiagonal_mul,sourceDiagonal_mul,sourceDiagonal_add]
  congr 1
  funext z
  change boolValue (listReset z.2.1.val z.2.2.val)=
    (1-boolValue (z.2.1.val.headD false))+boolValue (z.2.1.val.headD false)*
      (1-boolValue (z.2.2.val.headD false))*
      boolValue (listReset (listRotate z.2.1.val) (listRotate z.2.2.val))
  have hq := z.2.1.property
  have ht := z.2.2.property
  cases hqs : z.2.1.val with
  | nil => simp only [hqs,List.length_nil] at hq; omega
  | cons q qs =>
    cases hts : z.2.2.val with
    | nil => simp only [hts,List.length_nil] at ht; omega
    | cons t ts =>
      have he : qs.length=ts.length := by simp only [hqs,List.length_cons] at hq; simp only [hts,List.length_cons] at ht; omega
      simpa only [List.headD_cons] using listReset_real_rotation q t qs ts he

end
end E2.FiniteConstruction