import Lush.Crypto.SHA

namespace Lush.Crypto.HMAC

open Std
open BitVec
open Lush.Crypto.SHA

def blockLengthBytes := 64

def prepKey (key : ByteArray) : ByteArray :=
  let key :=
    if key.size ≤ blockLengthBytes
    then key
    else SHA.sha256 key
  let zeroPaddingLen := blockLengthBytes - key.size
  let zeroPadding := Array.replicate zeroPaddingLen 0 |> ByteArray.mk
  key ++ zeroPadding

theorem prepKey_size (key : ByteArray) : (prepKey key).size = blockLengthBytes := by
  have hreplicate (n : Nat) (a : UInt8) : (ByteArray.mk (Array.replicate n a)).size = n := by
    simp [←ByteArray.size_data]
  by_cases key.size ≤ 64
  <;> simp [prepKey, blockLengthBytes, *, size_sha256]

def sha256hmac (message : ByteArray) (key : ByteArray) : ByteArray :=
  let key := prepKey key
  let keyIpad := key.data.map (fun x => x ^^^ 0x36) |> ByteArray.mk
  let keyOpad := key.data.map (fun x => x ^^^ 0x5C) |> ByteArray.mk
  let innerHash := sha256 (keyIpad ++ message)
  let outerHash := sha256 (keyOpad ++ innerHash)
  outerHash

-- Test vector 1:
example :
    sha256hmac ("Hi There").toUTF8 (ByteArray.mk (Array.replicate 20 0x0b))
    = 0xb0344c61d8db38535ca8afceaf0bf12b881dc200c9833da726e9376c2e32cff7.toByteArray := by
  native_decide

-- Test vector 2:
example :
    sha256hmac "what do ya want for nothing?".toUTF8 "Jefe".toUTF8
    = 0x5bdcc146bf60754e6a042426089575c75a003f089d2739839dec58b964ec3843.toByteArray := by
  native_decide

-- Test vector 3:
-- Key: 20 bytes of 0xaa
-- Data: 50 bytes of 0xdd
example :
    sha256hmac
      (ByteArray.mk (Array.replicate 50 0xdd))
      (ByteArray.mk (Array.replicate 20 0xaa))
    = 0x773ea91e36800e46854db8ebd09181a72959098b3ef8c122d9635514ced565fe.toByteArray := by
  native_decide

-- Test vector 4:
-- Key: 0x01, 0x02, ..., 0x19 (25 bytes)
-- Data: 50 bytes of 0xcd
example :
    sha256hmac
      (ByteArray.mk (Array.replicate 50 0xcd))
      (ByteArray.mk #[
        0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08, 0x09,
        0x0a, 0x0b, 0x0c, 0x0d, 0x0e, 0x0f, 0x10, 0x11, 0x12,
        0x13, 0x14, 0x15, 0x16, 0x17, 0x18, 0x19
      ])
    = 0x82558a389a443c0ea4cc819899f2083a85f0faa3e578f8077a2e3ff46729665b.toByteArray := by
  native_decide

-- Test vector 5 (truncated output to 128 bits = first 16 bytes):
-- Key: 20 bytes of 0x0c
-- Data (ASCII): "Test With Truncation"
example :
    (sha256hmac
      "Test With Truncation".toUTF8
      (ByteArray.mk (Array.replicate 20 0x0c))
    ).extract 0 16
    = 0xa3b6167473100ee06e0c796c2955552b.toByteArray := by
  native_decide

-- Test vector 6:
-- Key: 131 bytes of 0xaa
-- Data (ASCII): "Test Using Larger Than Block-Size Key - Hash Key First"
example :
    sha256hmac
      "Test Using Larger Than Block-Size Key - Hash Key First".toUTF8
      (ByteArray.mk (Array.replicate 131 0xaa))
    = 0x60e431591ee0b67f0d8a26aacbf5b77f8e0bc6213728c5140546040f0ee37f54.toByteArray := by
  native_decide

-- Test vector 7:
-- Key: 131 bytes of 0xaa (same as test 6)
-- Data (ASCII): the long sentence from RFC 4231
example :
    sha256hmac
      "This is a test using a larger than block-size key and a larger than block-size data. The key needs to be hashed before being used by the HMAC algorithm.".toUTF8
      (ByteArray.mk (Array.replicate 131 0xaa))
    = 0x9b09ffa71b942fcb27635fbcd5b0e944bfdc63644f0713938a7f51535c3a35e2.toByteArray := by
  native_decide

end Lush.Crypto.HMAC
