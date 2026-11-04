import E2.FiniteBinaryDecoding
import E2.FiniteSourceDiagonal

namespace E2.FiniteConstruction
noncomputable section
open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator

theorem source_decoding_L_matrix (p : CounterProgram) (N : ℕ) (hN : 2≤N) (hEven : Even N) :
    sourceCore p N 15 =
      sourceCore p N 1*(1-sourceCore p N 2*sourceCore p N 1*(sourceCore p N 2).conjTranspose)+
      (1-sourceCore p N 1)*(1-sourceCore p N 2*sourceCore p N 1*(sourceCore p N 2).conjTranspose)*
        (sourceCore p N 2*(sourceCore p N 2*sourceCore p N 15*(sourceCore p N 2).conjTranspose)*
          (sourceCore p N 2).conjTranspose) := by
  let k := finiteSlots p N
  change sourceDiagonal N k (fun z => boolValue (decodedL z.1.1.val))=
    sourceDiagonal N k (fun z => boolValue (z.1.1.val.headD false))*
      (1-(sourcePerm N k (addressLift (addressRotation p N k))).permMatrix ℂ*
        sourceDiagonal N k (fun z => boolValue (z.1.1.val.headD false))*
        ((sourcePerm N k (addressLift (addressRotation p N k))).permMatrix ℂ).conjTranspose)+
    (1-sourceDiagonal N k (fun z => boolValue (z.1.1.val.headD false)))*
      (1-(sourcePerm N k (addressLift (addressRotation p N k))).permMatrix ℂ*
        sourceDiagonal N k (fun z => boolValue (z.1.1.val.headD false))*
        ((sourcePerm N k (addressLift (addressRotation p N k))).permMatrix ℂ).conjTranspose)*
      ((sourcePerm N k (addressLift (addressRotation p N k))).permMatrix ℂ*
        ((sourcePerm N k (addressLift (addressRotation p N k))).permMatrix ℂ*
          sourceDiagonal N k (fun z => boolValue (decodedL z.1.1.val))*
          ((sourcePerm N k (addressLift (addressRotation p N k))).permMatrix ℂ).conjTranspose)*
        ((sourcePerm N k (addressLift (addressRotation p N k))).permMatrix ℂ).conjTranspose)
  simp only [sourceConj_diagonal,sourceDiagonal_one_sub,sourceDiagonal_mul,sourceDiagonal_add]
  congr 1
  funext z
  change boolValue (decodedL z.1.1.val) = boolValue (z.1.1.val.headD false)*
    (1-boolValue ((listRotate z.1.1.val).headD false))+
    (1-boolValue (z.1.1.val.headD false))*(1-boolValue ((listRotate z.1.1.val).headD false))*
      boolValue (decodedL (listRotate (listRotate z.1.1.val)))
  have hl := z.1.1.property
  cases hb : z.1.1.val with
  | nil => simp only [hb,List.length_nil] at hl; omega
  | cons b cs =>
    cases hc : cs with
    | nil => simp only [hb,hc,List.length_cons,List.length_nil] at hl; omega
    | cons c bs =>
      have he : Even bs.length := by
        obtain ⟨m,hm⟩ := hEven
        simp only [hb,hc,List.length_cons] at hl
        exact ⟨m-1,by omega⟩
      simpa only [listRotate,List.cons_append,List.headD_cons] using binary_decoding_L b c bs he

theorem source_decoding_R_matrix (p : CounterProgram) (N : ℕ) (hN : 2≤N) (hEven : Even N) :
    sourceCore p N 16 =
      (1-(1-sourceCore p N 1)*(1-sourceCore p N 2*sourceCore p N 1*(sourceCore p N 2).conjTranspose))+
      (1/2:ℂ) • ((1-sourceCore p N 1)*(1-sourceCore p N 2*sourceCore p N 1*(sourceCore p N 2).conjTranspose)*
        (sourceCore p N 2*(sourceCore p N 2*sourceCore p N 16*(sourceCore p N 2).conjTranspose)*
          (sourceCore p N 2).conjTranspose)) := by
  let k := finiteSlots p N
  change sourceDiagonal N k (fun z => decodedR z.1.1.val)=
    (1-(1-sourceDiagonal N k (fun z => boolValue (z.1.1.val.headD false)))*
      (1-(sourcePerm N k (addressLift (addressRotation p N k))).permMatrix ℂ*
        sourceDiagonal N k (fun z => boolValue (z.1.1.val.headD false))*
        ((sourcePerm N k (addressLift (addressRotation p N k))).permMatrix ℂ).conjTranspose))+
    (1/2:ℂ) • ((1-sourceDiagonal N k (fun z => boolValue (z.1.1.val.headD false)))*
      (1-(sourcePerm N k (addressLift (addressRotation p N k))).permMatrix ℂ*
        sourceDiagonal N k (fun z => boolValue (z.1.1.val.headD false))*
        ((sourcePerm N k (addressLift (addressRotation p N k))).permMatrix ℂ).conjTranspose)*
      ((sourcePerm N k (addressLift (addressRotation p N k))).permMatrix ℂ*
        ((sourcePerm N k (addressLift (addressRotation p N k))).permMatrix ℂ*
          sourceDiagonal N k (fun z => decodedR z.1.1.val)*
          ((sourcePerm N k (addressLift (addressRotation p N k))).permMatrix ℂ).conjTranspose)*
        ((sourcePerm N k (addressLift (addressRotation p N k))).permMatrix ℂ).conjTranspose))
  simp only [sourceConj_diagonal,sourceDiagonal_one_sub,sourceDiagonal_mul]
  rw [show (1/2:ℂ)=(((1/2:ℝ):ℝ):ℂ) by norm_num,sourceDiagonal_real_smul,sourceDiagonal_add]
  congr 1
  funext z
  change decodedR z.1.1.val = (1-(1-boolValue (z.1.1.val.headD false))*
    (1-boolValue ((listRotate z.1.1.val).headD false)))+
    (1/2:ℝ)*((1-boolValue (z.1.1.val.headD false))*(1-boolValue ((listRotate z.1.1.val).headD false))*
      decodedR (listRotate (listRotate z.1.1.val)))
  have hl := z.1.1.property
  cases hb : z.1.1.val with
  | nil => simp only [hb,List.length_nil] at hl; omega
  | cons b cs =>
    cases hc : cs with
    | nil => simp only [hb,hc,List.length_cons,List.length_nil] at hl; omega
    | cons c bs =>
      have he : Even bs.length := by
        obtain ⟨m,hm⟩ := hEven
        simp only [hb,hc,List.length_cons] at hl
        exact ⟨m-1,by omega⟩
      have hd := binary_decoding_R b c bs he
      simpa only [listRotate,List.cons_append,List.headD_cons,mul_assoc] using hd

end
end E2.FiniteConstruction