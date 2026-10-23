import Bohr59aCore.Format

/-!
# Packed vertex keys (core Lean only)

`decK n` decodes a key of six components from one natural number, 16 bits per component (first component lowest):
bit 0 is `tan`, bits 1-4 are `j`, bits 5-15 are `m + 512`. The generated modules write keys as `decK (nat_lit n)`, which
elaborates far faster than six anonymous constructors. The decoder is untrusted: the kernel walk (`walkK2`) compares the
decoded keys with the leaf keys it computes, and the vertex theorems are stated for the same `decK` terms.
-/

namespace Bohr59aSplitK

open Bohr59aCore

/-- one key component from its 16-bit code -/
def decC (c : Nat) : Comp := ⟨c % 2 == 1, Int.subNatNat (c / 32 % 2048) 512, c / 2 % 16⟩

/-- a key of six components from its packed code -/
def decK (n : Nat) : List Comp :=
  [decC (n % 65536), decC (n / 65536 % 65536), decC (n / 4294967296 % 65536), decC (n / 281474976710656 % 65536),
   decC (n / 18446744073709551616 % 65536), decC (n / 1208925819614629174706176 % 65536)]

end Bohr59aSplitK
