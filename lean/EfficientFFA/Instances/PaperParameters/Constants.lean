import EfficientFFA.Native.EllipticCurve
import EfficientFFA.Multiplication
import EfficientFFA.Normalization

/-! Arithmetic configurations from the current paper's emulation table and
self-emulation paragraph. Field constants were cross-checked against arkworks'
field definitions, consulted 2026-11-12:
- https://docs.rs/ark-secp256k1/latest/src/ark_secp256k1/fields/fq.rs.html
- https://docs.rs/ark-bn254/latest/src/ark_bn254/fields/fq.rs.html
- https://docs.rs/ark-bn254/latest/src/ark_bn254/fields/fr.rs.html
- https://docs.rs/ark-bls12-381/latest/src/ark_bls12_381/fields/fq.rs.html
- https://docs.rs/ark-bls12-381/latest/src/ark_bls12_381/fields/fr.rs.html
The decimal constants are fixed below; no build downloads or trusts these sources.
These are integer arithmetic certificates, not primality or group-order proofs. -/
namespace EfficientFFA.Instances.PaperParameters

def secpQ : ℤ := 2^256 - 2^32 - 977
def bnQ : ℤ := 21888242871839275222246405745257275088696311157297823662689037894645226208583
def blsQ : ℤ := 4002409555221667393417789825735904156556882819939007885332058136124031650490837864442687629129015664037894272559787
def bnP : ℤ := 21888242871839275222246405745257275088548364400416034343698204186575808495617
def blsP : ℤ := 52435875175126190479447740508185965837690552500527637822603658699938581184513

/-- The two native scalar moduli used by the emulation table. -/
inductive NativeField where | bn | bls
  deriving DecidableEq

def NativeField.modulus : NativeField → ℤ
  | .bn => bnP
  | .bls => blsP

end EfficientFFA.Instances.PaperParameters
