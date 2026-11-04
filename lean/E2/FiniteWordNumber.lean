import E2.FiniteGuardMatrices
import E2.FiniteCyclicMask

namespace E2.FiniteConstruction
noncomputable section
open Fin.NatCast

def listNumber : List Bool → ℕ
  | [] => 0
  | false::bs => 2*listNumber bs
  | true::bs => 1+2*listNumber bs

theorem listNumber_lt (bs : List Bool) : listNumber bs < 2^bs.length := by
  induction bs with
  | nil => norm_num [listNumber]
  | cons b bs ih => cases b <;> simp only [listNumber,List.length_cons,pow_succ] <;> omega

theorem listNumber_injective (bs cs : List Bool) (hlen : bs.length=cs.length)
    (hnum : listNumber bs=listNumber cs) : bs=cs := by
  induction bs generalizing cs with
  | nil =>
    have hc : cs=[] := List.length_eq_zero_iff.mp hlen.symm
    exact hc.symm
  | cons b bs ih =>
    cases cs with
    | nil => simp at hlen
    | cons c cs =>
      have hl : bs.length=cs.length := by simpa using hlen
      cases b <;> cases c <;> simp only [listNumber] at hnum
      · exact congrArg (List.cons false) (ih cs hl (by omega))
      · omega
      · omega
      · exact congrArg (List.cons true) (ih cs hl (by omega))

theorem listNumber_increment (bs : List Bool) :
    listNumber (listIncrement bs) = if bs.all id then 0 else listNumber bs+1 := by
  induction bs with
  | nil => simp [listNumber,listIncrement]
  | cons b bs ih =>
    cases b
    · simp [listNumber,listIncrement]; omega
    · simp only [listNumber,listIncrement,List.all_cons,id_eq,Bool.true_and,ih]
      split_ifs <;> omega

theorem listNumber_all_ones (bs : List Bool) (h : bs.all id = true) :
    listNumber bs+1=2^bs.length := by
  induction bs with
  | nil => norm_num [listNumber]
  | cons b bs ih =>
    cases b
    · simp at h
    · simp only [List.all_cons,Bool.true_and] at h
      simp only [listNumber,List.length_cons,pow_succ]
      have := ih h
      omega

def wordNumber (N : ℕ) (b : BinaryWord N) : Fin (2^N) :=
  ⟨listNumber b.val,by simpa only [b.property] using listNumber_lt b.val⟩

theorem wordNumber_injective (N : ℕ) : Function.Injective (wordNumber N) := by
  intro b c he
  apply Subtype.ext
  exact listNumber_injective b.val c.val (b.property.trans c.property.symm) (congrArg Fin.val he)

def binaryNumberEquiv (N : ℕ) : BinaryWord N ≃ Fin (2^N) :=
  Equiv.ofBijective (wordNumber N) ((Fintype.bijective_iff_injective_and_card _).mpr
    ⟨wordNumber_injective N,by
      rw [Fintype.card_congr (Equiv.vectorEquivFin Bool N)]
      simp⟩)

theorem wordNumber_increment (N : ℕ) (b : BinaryWord N) :
    wordNumber N (incrementWord N b) = finRotate (2^N) (wordNumber N b) := by
  rw [finRotate_apply]
  apply Fin.ext
  change listNumber (listIncrement b.val) = (listNumber b.val+(1%2^N)) % 2^N
  rw [show (listNumber b.val+(1%2^N)) % 2^N = (listNumber b.val+1)%2^N by simp [Nat.add_mod]]
  rw [listNumber_increment]
  by_cases h : b.val.all id = true
  · have hn : listNumber b.val+1=2^N := by simpa only [b.property] using listNumber_all_ones b.val h
    simp [h,hn]
  · have hb := listNumber_lt (listIncrement b.val)
    rw [listIncrement_length,b.property,listNumber_increment] at hb
    simp only [h,↓reduceIte] at hb ⊢
    exact (Nat.mod_eq_of_lt hb).symm

end
end E2.FiniteConstruction