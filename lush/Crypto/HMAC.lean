import Lush.Crypto.SHA

namespace Lush.Crypto.HMAC

open Std
open BitVec
open Lush.Crypto.SHA

def blockLengthBytes := 64

def prepKey (key : ByteArray) (hlen : key.size < 2^61) : ByteArray :=
  let key :=
    if key.size ≤ blockLengthBytes
    then key
    else bitVecToByteArray (SHA.sha256 key hlen)
  let zeroPaddingLen := blockLengthBytes - key.size
  let zeroPadding := Array.replicate zeroPaddingLen 0 |> ByteArray.mk
  key ++ zeroPadding

def prep_key_size (key : ByteArray) (hlen : key.size < 2^61) :
    (prepKey key hlen).size = blockLengthBytes := by
  sorry

def ipad : ByteArray :=
  Array.replicate blockLengthBytes 0x36 |> ByteArray.mk

theorem size_ipad : ipad.size = blockLengthBytes := by
  simp [ipad]
  rw [←ByteArray.size_data, Array.size_replicate]

def opad : ByteArray :=
  Array.replicate blockLengthBytes 0x5C |> ByteArray.mk

theorem size_opad : opad.size = blockLengthBytes := by
  simp [opad]
  rw [←ByteArray.size_data, Array.size_replicate]

/-
TODO:
 - I need an easier way to do bitwise operations on ByteArrays.
 - Lemma for lengths of bytearray <-> bitvec conversions.
 - The length lemmas are annoying, maybe I just skip them? I'll silently
   create "wrong" hashes but they are still usable hashes, just non-compliant
   with the RFC.
-/

def sha256hmac
    (message : ByteArray)
    (key : ByteArray)
    (hlenmsg : message.size < 2^60)
    (hlenkey : key.size < 2^61) :
    ByteArray :=
  let key := prepKey key hlenkey
  let keyIpad :=
    ((byteArrayToBitVec key).cast (by sorry) : BitVec (8 * blockLengthBytes))
    ^^^ (byteArrayToBitVec ipad).cast (by sorry)
  let keyOpad :=
    ((byteArrayToBitVec key).cast (by sorry) : BitVec (8 * blockLengthBytes))
    ^^^ (byteArrayToBitVec opad).cast (by sorry)
  let innerHash := sha256 (bitVecToByteArray keyIpad ++ message) (by sorry)
  let outerHash := sha256 (bitVecToByteArray keyOpad ++ bitVecToByteArray innerHash) (by sorry)
  bitVecToByteArray outerHash

end Lush.Crypto.HMAC
