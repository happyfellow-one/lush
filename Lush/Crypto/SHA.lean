import Lush.Crypto.BitOperations
/-!
# SHA-256 Implementation

Performance is probably abysmal, there's just byte-level support.

Even though SHA-256 is specified only for inputs of less than 2^64
bits, the function does not check the length nor require a proof
that the length is in bounds: it'll produce "incorrect" output
(although you can also treat it as an extension to SHA-256, whatever
floats your boat).

All length variables are specified in bytes.
-/

namespace Lush.Crypto.SHA

open Std
open BitVec

def paddingNoLength (length : Nat) : {b : ByteArray // (length + b.size) % 64 = 56} :=
  let n :=
    if length % 64 < 56
    then 56 - (length % 64)
    else 56 + (64 - length % 64)
  have n_not_zero : n > 0 := by grind
  let b := ByteArray.mk (Array.replicate n 0)
  let blen : b.size = n := by simp [b, ←ByteArray.size_data]
  let b : ByteArray := b.set 0 0x80
  let prf : (length + b.size) % 64 = 56 := by
    unfold b
    simp [←ByteArray.size_data]
    grind
  ⟨b, prf⟩

example : (paddingNoLength 55).1 = ByteArray.mk #[0x80] := by native_decide
example : (paddingNoLength 54).1 = ByteArray.mk #[0x80, 0x00] := by native_decide

def padding (length : Nat) : {b : ByteArray // (length + b.size) % 64 = 0} :=
  let ⟨b, h⟩ := paddingNoLength length
  let b' := b ++ (ByteArray.mk (UInt64.toArrayBE (UInt64.ofNat (8*length))))
  have hlen : b'.size = b.size + 8 := by simp [b', UInt64.toArrayBE, ←ByteArray.size_data]
  have h' : (length + b'.size) % 64 = 0 := by grind
  ⟨b', h'⟩

def shaCh (x y z : BitVec 32) : BitVec 32 := (x &&& y) ||| (~~~x &&& z)
def shaMaj (x y z : BitVec 32) : BitVec 32 := (x &&& y) ^^^ (x &&& z) ^^^ (y &&& z)

def shaSigma₀ (x : BitVec 32) : BitVec 32 :=
  BitVec.rotateRight x 2
  ^^^ BitVec.rotateRight x 13
  ^^^ BitVec.rotateRight x 22

def shaSigma₁ (x : BitVec 32) : BitVec 32 :=
  BitVec.rotateRight x 6
  ^^^ BitVec.rotateRight x 11
  ^^^ BitVec.rotateRight x 25

def shasigma₀ (x : BitVec 32) : BitVec 32 :=
  BitVec.rotateRight x 7
  ^^^ BitVec.rotateRight x 18
  ^^^ BitVec.ushiftRight x 3

def shasigma₁ (x : BitVec 32) : BitVec 32 :=
  BitVec.rotateRight x 17
  ^^^ BitVec.rotateRight x 19
  ^^^ BitVec.ushiftRight x 10

def shaK : Array (BitVec 32) :=
  #[ 0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5
   , 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5
   , 0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3
   , 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174
   , 0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc
   , 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da
   , 0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7
   , 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967
   , 0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13
   , 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85
   , 0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3
   , 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070
   , 0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5
   , 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3
   , 0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208
   , 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2
   ]

theorem shaK_size : shaK.size = 64 := by simp [shaK]

structure ShaBlock where
  block : Array (BitVec 32)
  hlen : block.size = 16 := by grind
deriving Repr

def ShaBlock.ofBits (b : BitVec 512) : ShaBlock :=
  let block : Array (BitVec 32) :=
    Array.finRange 16 |>.map fun (i : Fin 16) =>
      let start := 512 - (i.toNat + 1)*32
      (b.extractLsb' start 32)
  have hlen : block.size = 16 := by
    unfold block
    rw [Array.size_map, Array.size_finRange]
  { block, hlen := hlen }

def concatBitVecArray'
    {n : Nat}
    (a : Array (BitVec n))
    (i : Nat)
    (hlen : i ≤ a.size)
    (acc : BitVec (i * n)) : BitVec (a.size * n) :=
  if heq : i = a.size
  then by rw [←heq]; exact acc
  else
    have hlen : i < a.size := by omega
    have heq : (i + 1) * n = i * n + n := by
      rw [Nat.mul_comm, Nat.mul_add]; simp; rw [Nat.mul_comm]
    let acc : BitVec ((i + 1) * n) :=  by
      rw [heq]
      exact acc ++ a[i]
    have hlen : i + 1 ≤ a.size := by omega
    concatBitVecArray' a (i+1) hlen acc

def concatBitVecArray {n : Nat} (a : Array (BitVec n)) : BitVec (a.size * n) :=
  concatBitVecArray' a 0 (by simp) (by simp; exact BitVec.ofNat 0 0)

structure MessageSchedule where
  schedule : Array (BitVec 32)
  hlen : schedule.size = 64 := by grind

def messageSchedule (block : ShaBlock) : MessageSchedule :=
  have hblocklen : block.block.size = 16 := block.hlen
  Id.run do
    let mut schedule : { a : Array (BitVec 32) // a.size = 64 } :=
      ⟨Array.replicate 64 (BitVec.zero 32), by trivial⟩
    for x in List.finRange 16 do
      schedule := ⟨schedule.val.set x (block.block[x]), by grind⟩
    for x' in List.finRange (64 - 16) do
      let x := x'.val + 16
      let val :=
        shasigma₁ (schedule.val[x-2])
        + schedule.val[x-7]
        + shasigma₀ (schedule.val[x-15])
        + schedule.val[x-16]
      schedule := ⟨schedule.val.set x val, by grind⟩
    return ⟨schedule, by grind⟩

structure ShaState where
  hash : Array (BitVec 32)
  hhashlen : hash.size = 8 := by grind

def ShaState.initial : ShaState :=
  let hash : Array (BitVec 32) :=
    #[  0x6a09e667
      , 0xbb67ae85
      , 0x3c6ef372
      , 0xa54ff53a
      , 0x510e527f
      , 0x9b05688c
      , 0x1f83d9ab
      , 0x5be0cd19 ]
  have hhashlen : hash.size = 8 := by simp [hash]
  { hash := hash }

def shaRound (state : ShaState) (block : ShaBlock) : ShaState :=
  let schedule := messageSchedule block
  let f (working : { a : Array (BitVec 32) // a.size = 8 }) (i : Fin 64) :=
    let ⟨working, hworkinglen⟩ := working
    have hschedulelen := schedule.hlen
    let getWorking (i : Fin 8) := working[i]'(by rw [hworkinglen]; apply Fin.is_lt i)
    let T1 :=
      getWorking 7
      + shaSigma₁ (getWorking 4)
      + shaCh (getWorking 4) (getWorking 5) (getWorking 6)
      + shaK[i.val]
      + schedule.schedule[i.val]'(by simp [schedule.hlen])
    let T2 :=
      shaSigma₀ (getWorking 0)
      + shaMaj (getWorking 0) (getWorking 1) (getWorking 2)
    let working :=
      #[ T1 + T2
       , getWorking 0
       , getWorking 1
       , getWorking 2
       , getWorking 3 + T1
       , getWorking 4
       , getWorking 5
       , getWorking 6
      ]
    have hworkinglen : working.size = 8 := by simp [working]
    ⟨working, hworkinglen⟩
  let working := (List.finRange 64).foldl f ⟨state.hash, state.hhashlen⟩
  have hworkinglen : working.val.size = 8 := by exact working.property
  let hash :=
    Array.mapFinIdx state.hash (fun i a hi =>
      have hlen : i < working.val.size := by
        rw [working.property]; rw [state.hhashlen] at hi; trivial
      a + working.val[i]
    )
  have hhashlen : hash.size = 8 := by unfold hash; simp; exact state.hhashlen
  { hash := hash, hhashlen := hhashlen }

def byteArrayToBitVec'
    (b : ByteArray)
    (i : Nat)
    (hi : i ≤ b.size)
    (acc : BitVec (8 * i)) : BitVec (8 * b.size) :=
  if heq : i = b.size
  then by rw [←heq]; exact acc
  else
    have hi : (i+1) ≤ b.size := by omega
    let acc := acc ++ (BitVec.ofNat 8 (UInt8.toNat b[i]))
    byteArrayToBitVec' b (i+1) hi acc

def byteArrayToBitVec (b : ByteArray) : BitVec (8 * b.size) :=
  byteArrayToBitVec' b 0 (by simp) (BitVec.ofNat 0 0)

-- If n % 8 != 0, then it'll be left padded with enough 0 bits on the left
-- (the hsb side).
def bitVecToByteArray {n : Nat} (b : BitVec n) : ByteArray :=
  let n' := (n + 7) / 8
  let b' : BitVec (8 * n') := b.setWidth (8 * n')
  Id.run do
    let mut out := ByteArray.empty
    for i in [0:n'] do
      let byte := (b' >>> (8*n' - 8 * (i + 1))).toNat &&& 0xFF |> UInt8.ofNat
      out := out.push byte
    return out

example : bitVecToByteArray (0b1010101010#10 : BitVec 10) = ByteArray.mk #[2, 170] := by
  native_decide

def messageToBlocks (message : ByteArray) : Array ShaBlock :=
  let n := message.size
  let ⟨padding, hpaddinglen⟩ := padding n
  let messageWithPadding := message ++ padding
  let numBlocks := messageWithPadding.size / 64
  Array.finRange numBlocks |>.map fun (i : Fin numBlocks) =>
    let blockBytes := messageWithPadding.extract (i*64) ((i+1)*64)
    have blockBytesLen : blockBytes.size = 64 := by
      unfold blockBytes
      rw [ByteArray.size_extract]
      omega
    ShaBlock.ofBits ((byteArrayToBitVec blockBytes).cast (by omega))

def sha256 (message : ByteArray) : ByteArray :=
  let blocks := messageToBlocks message
  let finalState := blocks.foldl shaRound ShaState.initial
  have hlen : finalState.hash.size * 32 = 256 := by simp [finalState.hhashlen]
  finalState.hash.flatMap (fun bv => UInt32.toArrayBE bv.toNat.toUInt32)
  |> ByteArray.mk

def size_sha256 (message : ByteArray) : (sha256 message).size = 32 := by
  unfold sha256
  simp [←ByteArray.size_data, UInt32.toArrayBE]
  conv => lhs; arg 1; arg 1; change Function.const _ 4
  simp [Array.map_const, ShaState.hhashlen]

@[grind! .]
theorem String.utf8LengthBoundedByLength (s : String) : s.utf8ByteSize ≤ 4*s.length := by
  apply String.push_induction
    (motive := fun s => s.utf8ByteSize ≤ 4*s.length)
  · simp
  · intro s c ih
    rw [String.length_push]
    rw [String.utf8ByteSize_push]
    have h : c.utf8Size ≤ 4 := by apply Char.utf8Size_le_four
    grind

def sha256String (input : String) : ByteArray := sha256 input.toUTF8

example :
    sha256 ByteArray.empty
    = 0xe3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855.toByteArray := by
  native_decide

example :
    sha256String (String.join (List.replicate 256 "HELLO"))
    = 0x8dc54998040d81bf0a1a317085396869292a285864c6080d3e40aec35ebea923.toByteArray := by
  native_decide

example :
    sha256String (String.join (List.replicate 2 "12345678901234567890123456789"))
    = 0xf55913b97a0c310ac5a5df4889c0c71474e6437e387f3cf1d6f074f6405fbf94.toByteArray := by
  native_decide

end Lush.Crypto.SHA
