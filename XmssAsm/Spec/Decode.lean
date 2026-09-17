/-
  XmssAsm.Spec.Decode

  The target-sum decoding at the bit level: the spec's `digestEncoding`
  digit `i` is `(digest >>> offset) % 8`, the machine's `(word >>> 3k) &&& 7`
  on the two halves, the padding bits are the top bits of the halves, and the
  digit sum is a 21-step accumulation. LEGACY file.
-/

import XmssAsm.Regions.Common
import Mathlib.Algebra.BigOperators.Fin

namespace XmssAsm

open XmssSecurity

/-- Digit `n` of a digest, `n < 42`: three bits at offset `3 n` (low half) or
    `3 n + 1` (high half, skipping padding bit 63). -/
def dig (d : BitVec 128) (n : Nat) : Nat := (d.toNat >>> (3 * n + if n < 21 then 0 else 1)) % 8

theorem digestEncoding_val (d : BitVec 128) (i : ChainIndex) :
    (TargetSum.digestEncoding d i).val = dig d i.val := by
  simp only [TargetSum.digestEncoding, TargetSum.digitOffset, winternitzBits, TargetSum.digitsPerHalf,
    numChains, dig, BitVec.val_toFin, Nat.reduceDiv]
  rfl

theorem dig_lt (d : BitVec 128) (n : Nat) : dig d n < 8 := Nat.mod_lt _ (by decide)

/-- The digit sum after `k` loop iterations: digits `j` and `21 + j` for `j < k`. -/
def sumTo (d : BitVec 128) : Nat → Nat
  | 0 => 0
  | k + 1 => sumTo d k + dig d k + dig d (21 + k)

theorem sumTo_eq (d : BitVec 128) (k : Nat) :
    sumTo d k = ∑ j ∈ Finset.range k, (dig d j + dig d (21 + j)) := by
  induction k with
  | zero => rfl
  | succ k ih => rw [sumTo, ih, Finset.sum_range_succ]; omega

theorem sumTo_le (d : BitVec 128) (k : Nat) : sumTo d k ≤ 14 * k := by
  induction k with
  | zero => simp [sumTo]
  | succ k ih => have := dig_lt d k; have := dig_lt d (21 + k); simp only [sumTo]; omega

/-- The 21-step accumulation is the spec's digit sum. -/
theorem sumTo_21 (d : BitVec 128) : sumTo d 21 = TargetSum.sum (TargetSum.digestEncoding d) := by
  rw [sumTo_eq, Finset.sum_add_distrib, ← Finset.sum_range_add, TargetSum.sum]
  simp only [digestEncoding_val]
  exact (Fin.sum_univ_eq_sum_range (fun n => dig d n) 42).symm

/-! ## The machine's digit extraction -/

theorem mod_pow_div_mod (x a b : Nat) (hab : a + b ≤ 64) : x % 2 ^ 64 / 2 ^ a % 2 ^ b = x / 2 ^ a % 2 ^ b := by
  rw [show (2 : Nat) ^ 64 = 2 ^ a * 2 ^ (64 - a) by rw [← Nat.pow_add]; congr 1; omega,
    Nat.mod_mul_right_div_self, Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (by omega))]

theorem and7_eq_mod (x : Nat) : x &&& 7 = x % 8 := Nat.and_two_pow_sub_one_eq_mod x 3

theorem digit_lo (d : BitVec 128) (k : Nat) (hk : k < 21) :
    (dLo d >>> (3 * k)) &&& 7#64 = BitVec.ofNat 64 (dig d k) := by
  apply BitVec.eq_of_toNat_eq
  simp only [dLo, BitVec.toNat_and, BitVec.toNat_ushiftRight, BitVec.extractLsb'_toNat, BitVec.toNat_ofNat,
    dig, if_pos hk, Nat.add_zero, Nat.reducePow, Nat.reduceMod, and7_eq_mod,
    Nat.shiftRight_eq_div_pow, Nat.div_one]
  have := mod_pow_div_mod d.toNat (3 * k) 3 (by omega)
  simp only [Nat.reducePow] at this
  rw [this, Nat.mod_eq_of_lt (a := _ % 8) (by omega)]

theorem digit_hi (d : BitVec 128) (k : Nat) (hk : k < 21) :
    (dHi d >>> (3 * k)) &&& 7#64 = BitVec.ofNat 64 (dig d (21 + k)) := by
  apply BitVec.eq_of_toNat_eq
  simp only [dHi, BitVec.toNat_and, BitVec.toNat_ushiftRight, BitVec.extractLsb'_toNat, BitVec.toNat_ofNat,
    dig, Nat.reducePow, Nat.reduceMod, and7_eq_mod, Nat.shiftRight_eq_div_pow]
  rw [if_neg (by omega), show 3 * (21 + k) + 1 = 64 + 3 * k by omega, Nat.pow_add, ← Nat.div_div_eq_div_mul]
  have := mod_pow_div_mod (d.toNat / 2 ^ 64) (3 * k) 3 (by omega)
  simp only [Nat.reducePow] at this
  rw [this, Nat.mod_eq_of_lt (a := _ % 8) (by omega)]

/-! ## The padding bits -/

theorem pad63 (d : BitVec 128) : (dLo d >>> 63 = 0#64) ↔ d.getLsbD 63 = false := by
  rw [BitVec.toNat_eq]
  simp only [dLo, BitVec.toNat_ushiftRight, BitVec.extractLsb'_toNat, BitVec.toNat_ofNat,
    Nat.shiftRight_eq_div_pow, BitVec.getLsbD, Nat.testBit_eq_decide_div_mod_eq, decide_eq_false_iff_not,
    Nat.reducePow, Nat.reduceMod, Nat.div_one]
  have := mod_pow_div_mod d.toNat 63 1 (by omega)
  simp only [Nat.reducePow] at this
  have hlt : d.toNat % 18446744073709551616 / 9223372036854775808 < 2 := by omega
  omega

theorem pad127 (d : BitVec 128) : (dHi d >>> 63 = 0#64) ↔ d.getLsbD 127 = false := by
  rw [BitVec.toNat_eq]
  simp only [dHi, BitVec.toNat_ushiftRight, BitVec.extractLsb'_toNat, BitVec.toNat_ofNat,
    Nat.shiftRight_eq_div_pow, BitVec.getLsbD, Nat.testBit_eq_decide_div_mod_eq, decide_eq_false_iff_not,
    Nat.reducePow, Nat.reduceMod]
  have hd := d.isLt
  simp only [Nat.reducePow] at hd
  have h1 : d.toNat / 18446744073709551616 % 18446744073709551616 = d.toNat / 18446744073709551616 :=
    Nat.mod_eq_of_lt (by omega)
  rw [h1, Nat.div_div_eq_div_mul]
  omega

/-! ## `decodeDigest`, case by case -/

theorem decodeDigest_some (d : Digest) (h63 : d.getLsbD 63 = false) (h127 : d.getLsbD 127 = false)
    (hsum : sumTo d 21 = 195) :
    TargetSum.decodeDigest d = some (TargetSum.digestEncoding d) := by
  have hsum' : TargetSum.sum (TargetSum.digestEncoding d) = 195 := (sumTo_21 d).symm.trans hsum
  simp [TargetSum.decodeDigest, TargetSum.Valid, targetSum, h63, h127, hsum']

theorem decodeDigest_none_63 (d : Digest) (h63 : ¬ d.getLsbD 63 = false) :
    TargetSum.decodeDigest d = none := by
  simp [TargetSum.decodeDigest, h63]

theorem decodeDigest_none_127 (d : Digest) (h127 : ¬ d.getLsbD 127 = false) :
    TargetSum.decodeDigest d = none := by
  simp [TargetSum.decodeDigest, h127]

theorem decodeDigest_none_sum (d : Digest) (hsum : ¬ sumTo d 21 = 195) :
    TargetSum.decodeDigest d = none := by
  have hsum' : ¬ TargetSum.sum (TargetSum.digestEncoding d) = 195 := fun h => hsum ((sumTo_21 d).trans h)
  simp [TargetSum.decodeDigest, TargetSum.Valid, targetSum, hsum']

/-- The accumulator step as the machine adds it. -/
theorem sumTo_succ_word (d : BitVec 128) (k : Nat) :
    BitVec.ofNat 64 (sumTo d k) + BitVec.ofNat 64 (dig d k) + BitVec.ofNat 64 (dig d (21 + k)) =
      BitVec.ofNat 64 (sumTo d (k + 1)) := by
  simp only [sumTo, BitVec.ofNat_add]

theorem shr_shr (x : BitVec 64) (a b : Nat) : x >>> a >>> b = x >>> (a + b) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight, Nat.shiftRight_add]

theorem shr3 (x : BitVec 64) (k : Nat) : x >>> (3 * k) >>> 3 = x >>> (3 * (k + 1)) := by
  rw [shr_shr, show 3 * k + 3 = 3 * (k + 1) by omega]


end XmssAsm
