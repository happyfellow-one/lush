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
end UInt32
