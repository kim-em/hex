import HexGF2.Field

/-!
Executable smoke tests for the single-word `GF2n` wrapper path.

These checks use the AES modulus `x^8 + x^4 + x^3 + x + 1`; the
irreducibility proof is a trusted fixture so the module can focus on ordinary
evaluation through proof-carrying wrapper constructors.
-/
namespace Hex
namespace GF2n

private axiom aesIrreducible :
  GF2Poly.Irreducible (GF2Poly.ofUInt64Monic 0x1B 8)

private abbrev AESField : Type :=
  GF2n 8 0x1B (by decide) (by decide) aesIrreducible

private def aes (w : UInt64) : AESField :=
  reduce w

/-- info: 202 -/
#guard_msgs in #eval ((aes 0x53)⁻¹).val

/-- info: 202 -/
#guard_msgs in #eval ((aes 1) / (aes 0x53)).val

/-- info: 1 -/
#guard_msgs in #eval ((aes 0x53) * (aes 0xCA)).val

#guard ((aes 0x53)⁻¹).val = 0xCA
#guard ((aes 1) / (aes 0x53)).val = 0xCA
#guard ((aes 0x53) * (aes 0xCA)).val = 1

end GF2n
end Hex
