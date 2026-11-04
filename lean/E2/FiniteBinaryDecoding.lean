import E2.FiniteSourceTuple

namespace E2.FiniteConstruction
noncomputable section

theorem binaryDecode_append_zero_pair (bs : List Bool) (hE : Even bs.length) :
    binaryDecode (bs++[false,false])=binaryDecode bs := by
  induction bs using List.twoStepInduction with
  | nil => simp [binaryDecode]
  | singleton b => obtain ⟨n,hn⟩ := hE; simp only [List.length_singleton] at hn; omega
  | cons_cons b c bs ih _ =>
    have htail : Even bs.length := by
      obtain ⟨n,hn⟩ := hE
      exact ⟨n-1,by simp only [List.length_cons] at hn; omega⟩
    cases b <;> cases c <;> simp [binaryDecode,ih htail]

theorem decodedL_zero_pair (bs : List Bool) :
    decodedL (false::false::bs)=decodedL bs := by
  unfold decodedL
  cases h : binaryDecode bs <;> simp [binaryDecode,h]

theorem decodedR_zero_pair (bs : List Bool) :
    decodedR (false::false::bs)=(1/2:ℝ)*decodedR bs := by
  unfold decodedR
  cases h : binaryDecode bs with
  | none => simp [binaryDecode,h]
  | some z => simp [binaryDecode,h,counterCoordinate_succ]

theorem listRotate_twice (b c : Bool) (bs : List Bool) :
    listRotate (listRotate (b::c::bs))=bs++[b,c] := by
  simp [listRotate,List.append_assoc]

theorem binary_decoding_L (b c : Bool) (bs : List Bool) (hE : Even bs.length) :
    boolValue (decodedL (b::c::bs)) = boolValue b*(1-boolValue c)+
      (1-boolValue b)*(1-boolValue c)*
        boolValue (decodedL (listRotate (listRotate (b::c::bs)))) := by
  cases b <;> cases c
  · rw [decodedL_zero_pair,listRotate_twice]
    have he : decodedL (bs++[false,false])=decodedL bs := by
      unfold decodedL
      rw [binaryDecode_append_zero_pair bs hE]
    rw [he]
    norm_num [boolValue]
  · norm_num [decodedL,binaryDecode,boolValue]
  · norm_num [decodedL,binaryDecode,boolValue]
  · norm_num [decodedL,binaryDecode,boolValue]

theorem binary_decoding_R (b c : Bool) (bs : List Bool) (hE : Even bs.length) :
    decodedR (b::c::bs) = (1-(1-boolValue b)*(1-boolValue c))+
      (1/2:ℝ)*(1-boolValue b)*(1-boolValue c)*
        decodedR (listRotate (listRotate (b::c::bs))) := by
  cases b <;> cases c
  · rw [decodedR_zero_pair,listRotate_twice]
    have he : decodedR (bs++[false,false])=decodedR bs := by
      unfold decodedR
      rw [binaryDecode_append_zero_pair bs hE]
    rw [he]
    norm_num [boolValue]
  · norm_num [decodedR,binaryDecode,counterCoordinate,boolValue]
  · norm_num [decodedR,binaryDecode,counterCoordinate,boolValue]
  · norm_num [decodedR,binaryDecode,counterCoordinate,boolValue]

end
end E2.FiniteConstruction