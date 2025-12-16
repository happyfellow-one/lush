import Lush.Crypto.BitOperations

structure GF256 where
  val : UInt8
deriving Repr, BEq, DecidableEq, Inhabited

namespace GF256

@[simp] def ofUInt8 (x : UInt8) : GF256 := ⟨x⟩
@[simp] def toUInt8 (x : GF256) : UInt8 := x.val

instance : Coe GF256 UInt8 where
  coe x := x.val

instance : Coe UInt8 GF256 where
  coe x := ⟨x⟩

def add (a b : GF256) : GF256 :=
  ⟨a.val ^^^ b.val⟩

private def xtime (x : UInt8) : UInt8 :=
  let shifted : UInt8 := x <<< 1
  if (x &&& 0x80) ≠ 0
  then shifted ^^^ 0x1b
  else shifted

def mul (a b : GF256) : GF256 :=
  Id.run do
    let mut acc : UInt8 := 0
    let mut x   : UInt8 := a.val
    let mut y   : UInt8 := b.val
    for _ in [:8] do
      if (y &&& 1) ≠ 0 then
        acc := acc ^^^ x
      x := xtime x
      y := y >>> 1
    ⟨acc⟩

instance : Zero GF256 where
  zero := ⟨0⟩

instance : One GF256 where
  one := ⟨1⟩

instance : Add GF256 where
  add := add

instance : Mul GF256 where
  mul := mul

instance : Neg GF256 where
  neg a := a

instance : Sub GF256 where
  sub a b := add a b

instance : OfNat GF256 (nat_lit 0) where
  ofNat := 0

instance : OfNat GF256 (nat_lit 1) where
  ofNat := 1

end GF256

namespace Lush.Crypto.AES

-- All sizes are in bytes.

@[simp] def blockSize := 16
@[simp] def keySize := 16
@[simp] def numRounds := 10

def sboxMapping : Array UInt8 :=
#[
  0x63, 0x7c, 0x77, 0x7b, 0xf2, 0x6b, 0x6f, 0xc5, 0x30, 0x01, 0x67, 0x2b, 0xfe, 0xd7, 0xab, 0x76,
  0xca, 0x82, 0xc9, 0x7d, 0xfa, 0x59, 0x47, 0xf0, 0xad, 0xd4, 0xa2, 0xaf, 0x9c, 0xa4, 0x72, 0xc0,
  0xb7, 0xfd, 0x93, 0x26, 0x36, 0x3f, 0xf7, 0xcc, 0x34, 0xa5, 0xe5, 0xf1, 0x71, 0xd8, 0x31, 0x15,
  0x04, 0xc7, 0x23, 0xc3, 0x18, 0x96, 0x05, 0x9a, 0x07, 0x12, 0x80, 0xe2, 0xeb, 0x27, 0xb2, 0x75,
  0x09, 0x83, 0x2c, 0x1a, 0x1b, 0x6e, 0x5a, 0xa0, 0x52, 0x3b, 0xd6, 0xb3, 0x29, 0xe3, 0x2f, 0x84,
  0x53, 0xd1, 0x00, 0xed, 0x20, 0xfc, 0xb1, 0x5b, 0x6a, 0xcb, 0xbe, 0x39, 0x4a, 0x4c, 0x58, 0xcf,
  0xd0, 0xef, 0xaa, 0xfb, 0x43, 0x4d, 0x33, 0x85, 0x45, 0xf9, 0x02, 0x7f, 0x50, 0x3c, 0x9f, 0xa8,
  0x51, 0xa3, 0x40, 0x8f, 0x92, 0x9d, 0x38, 0xf5, 0xbc, 0xb6, 0xda, 0x21, 0x10, 0xff, 0xf3, 0xd2,
  0xcd, 0x0c, 0x13, 0xec, 0x5f, 0x97, 0x44, 0x17, 0xc4, 0xa7, 0x7e, 0x3d, 0x64, 0x5d, 0x19, 0x73,
  0x60, 0x81, 0x4f, 0xdc, 0x22, 0x2a, 0x90, 0x88, 0x46, 0xee, 0xb8, 0x14, 0xde, 0x5e, 0x0b, 0xdb,
  0xe0, 0x32, 0x3a, 0x0a, 0x49, 0x06, 0x24, 0x5c, 0xc2, 0xd3, 0xac, 0x62, 0x91, 0x95, 0xe4, 0x79,
  0xe7, 0xc8, 0x37, 0x6d, 0x8d, 0xd5, 0x4e, 0xa9, 0x6c, 0x56, 0xf4, 0xea, 0x65, 0x7a, 0xae, 0x08,
  0xba, 0x78, 0x25, 0x2e, 0x1c, 0xa6, 0xb4, 0xc6, 0xe8, 0xdd, 0x74, 0x1f, 0x4b, 0xbd, 0x8b, 0x8a,
  0x70, 0x3e, 0xb5, 0x66, 0x48, 0x03, 0xf6, 0x0e, 0x61, 0x35, 0x57, 0xb9, 0x86, 0xc1, 0x1d, 0x9e,
  0xe1, 0xf8, 0x98, 0x11, 0x69, 0xd9, 0x8e, 0x94, 0x9b, 0x1e, 0x87, 0xe9, 0xce, 0x55, 0x28, 0xdf,
  0x8c, 0xa1, 0x89, 0x0d, 0xbf, 0xe6, 0x42, 0x68, 0x41, 0x99, 0x2d, 0x0f, 0xb0, 0x54, 0xbb, 0x16
]

set_option maxRecDepth 10000 in
theorem size_sboxMapping : sboxMapping.size = 256 := by
  unfold sboxMapping
  native_decide

def sbox (x : GF256) : GF256 :=
  have h : x.val.toNat < sboxMapping.size := by rw [size_sboxMapping]; apply UInt8.toNat_lt
  GF256.ofUInt8 (sboxMapping[x.val.toNat]'h)

namespace KeyExpansion

def Rcon : Array UInt32 :=
  #[ 0x01000000
   , 0x02000000
   , 0x04000000
   , 0x08000000
   , 0x10000000
   , 0x20000000
   , 0x40000000
   , 0x80000000
   , 0x1b000000
   , 0x36000000
  ]

theorem size_Rcon : Rcon.size = 10 := by simp [Rcon]

private def rotWord (w : UInt32) := (w.toBitVec.rotateLeft 8).toNat.toUInt32

example : rotWord 0x09cf4f3c = 0xcf4f3c09 := by native_decide

private def subWord (w : UInt32) : UInt32 :=
  let w' := w.toArrayBE.map (fun x => (sbox (GF256.ofUInt8 x)).toUInt8)
  have : w'.size = 4 := by simp [w', Array.size_map, UInt32.size_toArrayBE]
  (w'[0].toUInt32 <<< 24)
  ||| (w'[1].toUInt32 <<< 16)
  ||| (w'[2].toUInt32 <<< 8)
  ||| w'[3].toUInt32

example : subWord 0xcf4f3c09 = 0x8a84eb01 := by native_decide

def expand
    (key : ByteArray)
    (hkeysize : key.size = keySize) :
    Array UInt32 :=
  let key :=
    #[ UInt32.ofArrayBE (key.extract 0 4)   (by simp [ByteArray.size_extract, hkeysize])
     , UInt32.ofArrayBE (key.extract 4 8)   (by simp [ByteArray.size_extract, hkeysize])
     , UInt32.ofArrayBE (key.extract 8 12)  (by simp [ByteArray.size_extract, hkeysize])
     , UInt32.ofArrayBE (key.extract 12 16) (by simp [ByteArray.size_extract, hkeysize])
    ]
  let Nk := keySize / 4
  have hkeylen : key.size = Nk := by unfold key Nk; simp
  Id.run do
    let mut w : { w : Array UInt32 // w.size = 4*numRounds + 4 } :=
      ⟨Array.replicate (4*numRounds + 4) 0, by simp⟩
    for i in List.finRange (keySize / 4) do
      have _ : i.val < 4 := by simp
      have h : i < 4*numRounds + 4 := by simp; omega
      let w' := ⟨w.val.set i key[i], by simp [Array.size_set, w.property]⟩
      w := w'

    for fi in List.finRange (4*numRounds + 4 - keySize / 4) do
      let i := fi + keySize / 4
      let mut temp := w.val[i-1]
      have _ : i/Nk - 1 < Rcon.size := by simp [size_Rcon, Nk, i]; omega
      if i % Nk = 0
      then temp := subWord (rotWord temp) ^^^ (Rcon[i/Nk - 1])
      let w' := w.val.set i (w.val[i - Nk] ^^^ temp)
      w := ⟨w', by simp [w', Array.size_set, w.property]⟩
    return w.val

theorem size_expand
    (key : ByteArray)
    (hkeysize : key.size = keySize)
    : (expand key hkeysize).size = 4*numRounds + 4 := by
  sorry

-- Taken from the NIST pdf example:
example :
    (expand 0x2b7e151628aed2a6abf7158809cf4f3c.toByteArray (by sorry)).drop 41
    = #[ 0xc9ee2589, 0xe13f0cc8, 0xb6630ca6 ] := by
  native_decide

end KeyExpansion

structure State where
  val : Array GF256
  hvalsize : val.size = 16 := by grind

namespace State

def index
    (state : State)
    (row : Nat)
    (col : Nat)
    (hrowlen : row < 4 := by grind)
    (hcollen : col < 4 := by grind) :
    GF256 :=
  let i := row + 4*col
  have hlen : i < state.val.size := by rw [state.hvalsize]; omega
  state.val[row + 4*col]

def ofByteArray (b : ByteArray) (h : b.size = 16) : State :=
  let val := b.data.map GF256.ofUInt8
  have hvalsize : val.size = 16 := by unfold val; simp; exact h
  ⟨val, hvalsize⟩

def toByteArray (state : State) : ByteArray :=
  state.val.map GF256.toUInt8 |> ByteArray.mk

def subBytes (state : State) : State :=
  let state' := state.val.map sbox
  have h : state'.size = 16 := by unfold state'; simp [state.hvalsize]
  ⟨state', h⟩

def shiftRows (state : State) : State :=
  Id.run do
    let mut state' : { a : Array GF256 // a.size = 16 } := ⟨Array.replicate 16 0, by simp⟩
    for i in List.finRange 4 do
      for j in List.finRange 4 do
        let row := i.val
        let col := (i.val + j.val) % 4
        have _ : row + 4*col < state.val.size := by unfold row col; simp [state.hvalsize]; omega
        have _ : row < 4 := by omega
        have _ : col < 4 := by omega
        let elem := state.index row col (by trivial) (by trivial)
        state' := ⟨state'.val.set (i + 4*j) elem, by simp [Array.size_set, state'.property]⟩
    return ⟨state'.val, state'.property⟩

example :
    let state :=
      ofByteArray
        (Array.range 16 |>.map (·.toUInt8) |> ByteArray.mk)
        (by simp [←ByteArray.size_data])
    let state' :=
      ofByteArray
        (ByteArray.mk
          #[ 0, 5, 10, 15,
             4, 9, 14, 3,
             8, 13, 2, 7,
             12, 1, 6, 11 ])
        (by simp [←ByteArray.size_data])
    state.shiftRows.val = state'.val := by
  native_decide

example :
    let state :=
      ofByteArray
        (Array.range 16 |>.map (·.toUInt8) |> ByteArray.mk)
        (by simp [←ByteArray.size_data])
    state.shiftRows.shiftRows.shiftRows.shiftRows.val = state.val := by
  native_decide

def mixColumnsMatrixRow : Array GF256 :=
  #[ 0x02, 0x03, 0x01, 0x01 ].map GF256.ofUInt8

def arrayRotateRight (a : Array α) (n : Nat) : Array α :=
  let n := n % a.size
  a.extract (a.size - n) a.size ++ a.extract 0 (a.size - n)

theorem size_arrayRotateRight (a : Array α) (n : Nat) :
    (arrayRotateRight a n).size = a.size := by
  simp [arrayRotateRight, Array.size_extract]

def arrayDot (a b : Array GF256) (h : a.size = b.size) : GF256 :=
  (List.finRange a.size).map (fun i => a[i] * b[i])
  |>.sum

def arrayAdd (a b : Array GF256) (h : a.size = b.size) : Array GF256 :=
  ((List.finRange a.size).map (fun (i : Fin a.size) => a[i] + b[i])).toArray

def mixColumns (state : State) : State :=
  let state :=
    (List.finRange 4).map (fun (j : Fin 4) =>
      let column := state.val.extract (4*j.val) (4*(j.val + 1))
      (List.finRange 4).map (fun (i : Fin 4) =>
        let vector := arrayRotateRight mixColumnsMatrixRow i
        have _ : column.size = vector.size := by
          simp [column, vector, state.hvalsize, size_arrayRotateRight, mixColumnsMatrixRow]
          omega
        arrayDot column vector (by trivial))
        |>.toArray)
    |>.foldl (· ++ ·) Array.empty
  ⟨state, by simp [state, List.foldl, List.map, List.finRange]; decide⟩

example :
    (ofByteArray 0x09287F476F746ABF2C4A6204DA08E3EE.toByteArray (by sorry)
    |> mixColumns |>.val)
    = (ofByteArray 0x529F16C2978615CAE01AAE54BA1A2659.toByteArray (by sorry)
       |>.val) := by
  native_decide

def addRoundKey
    (state : State)
    (roundKeys : Array UInt32)
    (hkeyssize : roundKeys.size = 4)
    : State :=
  let state' :=
    (List.finRange 4).map (fun (j : Fin 4) =>
      let column := state.val.extract (4*j.val) (4*(j.val + 1))
      let keyVector := roundKeys[j].toArrayBE.map GF256.ofUInt8
      have _ : column.size = keyVector.size := by
        simp [column, UInt32.size_toArrayBE, state.hvalsize, keyVector]
        omega
      arrayAdd column keyVector (by trivial))
    |>.foldl (· ++ ·) Array.empty
  ⟨state', by simp [state', List.foldl, List.map, List.finRange, arrayAdd, state.hvalsize]; decide⟩

end State

def encrypt
    (data : ByteArray)
    (hdatasize : data.size = blockSize)
    (key : ByteArray)
    (hkeysize : key.size = keySize)
    : ByteArray :=
  let state := State.mk (data.data.map GF256.ofUInt8) (by simp [hdatasize])
  let w := KeyExpansion.expand key hkeysize
  have hwsize : w.size = 44 := by simp [w, KeyExpansion.size_expand]
  let state := state.addRoundKey (w.extract 0 4) (by simp [w, KeyExpansion.size_expand])
  let state :=
    Id.run do
      let mut s := state
      for i in List.finRange (numRounds - 1) do
        let round := i.val + 1
        let roundKey := w.extract (4*round) (4*round + 4)
        have h : roundKey.size = 4 := by
          simp [hwsize, roundKey, round]
          omega
        s := s.subBytes.shiftRows.mixColumns.addRoundKey roundKey h
      let roundKey := w.extract (4*numRounds) (4*numRounds + 4)
      have h : roundKey.size = 4 := by
        unfold roundKey
        simp [Array.size_extract, hwsize, numRounds]
      s := s.subBytes.shiftRows.addRoundKey roundKey h
      return s
  state.toByteArray

example :
    let key := 0x2B7E151628AED2A6ABF7158809CF4F3C.toByteArray
    let plaintext := 0x6BC1BEE22E409F96E93D7E117393172A.toByteArray
    let encrypted := encrypt plaintext (by native_decide) key (by native_decide)
    let expected := 0x3AD77BB40D7A3660A89ECAF32466EF97.toByteArray
    encrypted = expected := by
  native_decide

end Lush.Crypto.AES
