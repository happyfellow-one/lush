namespace UInt64
def toArrayBE (n : UInt64) : Array UInt8 :=
  #[ (n >>> (8 * 7)).toUInt8
   , (n >>> (8 * 6)).toUInt8
   , (n >>> (8 * 5)).toUInt8
   , (n >>> (8 * 4)).toUInt8
   , (n >>> (8 * 3)).toUInt8
   , (n >>> (8 * 2)).toUInt8
   , (n >>> (8 * 1)).toUInt8
   , (n >>> (8 * 0)).toUInt8
  ]
end UInt64

namespace UInt32
def toArrayBE (n : UInt32) : Array UInt8 :=
  #[ (n >>> (8 * 3)).toUInt8
   , (n >>> (8 * 2)).toUInt8
   , (n >>> (8 * 1)).toUInt8
   , (n >>> (8 * 0)).toUInt8
  ]

theorem size_toArrayBE (n : UInt32) : n.toArrayBE.size = 4 := by simp [toArrayBE]

def ofArrayBE (b : ByteArray) (h : b.size = 4) : UInt32 :=
  (b[0].toUInt32 <<< 24)
  ||| (b[1].toUInt32 <<< 16)
  ||| (b[2].toUInt32 <<< 8)
  ||| b[3].toUInt32

end UInt32

namespace Nat

def toByteArray (n : Nat) : ByteArray :=
  Id.run do
    let mut b := ByteArray.empty
    let mut n := n
    while n > 0 do
      let byte := (n &&& 0xFF).toUInt8
      b := b.push byte
      n := n >>> 8
    return (b.data.reverse |> ByteArray.mk)

def toHexDigit (n : Nat) : String :=
  if n < 10 then toString n
  else if n = 10 then "a"
  else if n = 11 then "b"
  else if n = 12 then "c"
  else if n = 13 then "d"
  else if n = 14 then "e"
  else if n = 15 then "f"
  else "-"

def toHex (n : Nat) : String :=
  Id.run do
    let mut n := n
    let mut s := []
    while n > 0 do
      s := (n % 16).toHexDigit :: s
      n := n / 16
    return String.join s

end Nat

namespace ByteArray

def toNat (b : ByteArray) : Nat :=
  Id.run do
    let mut n := 0
    for i in List.finRange b.size do
      n := (n <<< 8) ||| b[i].toNat
    n

end ByteArray
