/-
Copyright (c) 2023 María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández
-/
module

public import Mathlib.RingTheory.DedekindDomain.AdicValuation
public import Mathlib.RingTheory.DedekindDomain.Factorization
public import Mathlib.Topology.Algebra.RestrictedProduct.TopologicalSpace
public import Mathlib.RingTheory.Valuation.Integers

/-!
# The finite adèle ring of a Dedekind domain
We define the ring of finite adèles of a Dedekind domain `R`.

## Main definitions
- `IsDedekindDomain.FiniteAdeleRing` : The finite adèle ring of `R`, defined as the
  restricted product `Πʳ_v K_v`. We give this ring a `K`-algebra structure.

## Implementation notes
We are only interested on Dedekind domains of Krull dimension 1 (i.e., not fields). If `R` is a
field, its finite adèle ring is just defined to be the trivial ring.

## References
* [J.W.S. Cassels, A. Fröhlich, *Algebraic Number Theory*][cassels1967algebraic]

## Tags
finite adèle ring, dedekind domain
-/

@[expose] public section

variable (R : Type*) [CommRing R] [IsDedekindDomain R] {K : Type*}
    [Field K] [Algebra R K] [IsFractionRing R K]

namespace IsDedekindDomain

/--
The support of an element `k` of the field of fractions of a Dedekind domain is
the set of maximal ideals of the Dedekind domain at which `k` is not integral.
-/
def HeightOneSpectrum.Support (k : K) : Set (HeightOneSpectrum R) :=
    {v : HeightOneSpectrum R | 1 < v.valuation K k}

/--
The support of an element of the field of fractions of a Dedekind domain
is finite.
-/
lemma HeightOneSpectrum.Support.finite (k : K) : (Support R k).Finite := by
  -- We write k=n/d.
  obtain ⟨⟨n, ⟨d, hd⟩⟩, hk⟩ := IsLocalization.surj (nonZeroDivisors R) k
  have hd' : d ≠ 0 := nonZeroDivisors.ne_zero hd
  suffices {v : HeightOneSpectrum R | v.valuation K (algebraMap R K d) < 1}.Finite by
    apply Set.Finite.subset this
    intro v hv
    apply_fun v.valuation K at hk
    simp only [Valuation.map_mul, valuation_of_algebraMap] at hk
    rw [Set.mem_setOf_eq, valuation_of_algebraMap]
    have := intValuation_le_one v n
    contrapose! this
    rw [← hk, mul_comm]
    exact (lt_mul_of_one_lt_right (by simp) hv).trans_le <|
      mul_le_mul_of_nonneg_right this (by simp)
  simp_rw [valuation_lt_one_iff_dvd]
  apply Ideal.finite_factors
  simpa only [Submodule.zero_eq_bot, ne_eq, Ideal.span_singleton_eq_bot]

end IsDedekindDomain

noncomputable section

open Function Set IsDedekindDomain.HeightOneSpectrum

namespace IsDedekindDomain

variable (K)

open scoped RestrictedProduct

/-! ### The finite adèle ring of a Dedekind domain
We define the finite adèle ring of `R` as the restricted product over all maximal ideals `v` of `R`
of `adicCompletion` with respect to `adicCompletionIntegers`. We prove that it is a commutative
ring. -/

/--
If `K` is the field of fractions of the Dedekind domain `R` then `FiniteAdeleRing R K` is
the ring of finite adeles of `K`, defined as the restricted product of the completions
`K_v` with respect to the subrings `R_v`. Here `v` runs through the nonzero primes of `R`
and the restricted product is the subring of `∏_v K_v` consisting of elements which
are in `R_v` for all but finitely many `v`.
-/
def FiniteAdeleRing : Type _ :=
  Πʳ v : HeightOneSpectrum R, [v.adicCompletion K, v.adicCompletionIntegers K]

instance : CommRing (FiniteAdeleRing R K) := inferInstanceAs <|
  CommRing <| Πʳ v : HeightOneSpectrum R, [v.adicCompletion K, v.adicCompletionIntegers K]

instance : TopologicalSpace (FiniteAdeleRing R K) := inferInstanceAs <|
  TopologicalSpace <| Πʳ v : HeightOneSpectrum R, [v.adicCompletion K, v.adicCompletionIntegers K]

instance : DFunLike (FiniteAdeleRing R K) (HeightOneSpectrum R) (fun v ↦ v.adicCompletion K) :=
  inferInstanceAs <|
  DFunLike (Πʳ v : HeightOneSpectrum R, [v.adicCompletion K, v.adicCompletionIntegers K])
    (HeightOneSpectrum R) (fun v ↦ v.adicCompletion K)

namespace FiniteAdeleRing

/--
The canonical map from `K` to the finite adeles of `K`.

The content of the existence of this map is the fact that an element `k` of `K` is integral at
all but finitely many places, which is `IsDedekindDomain.HeightOneSpectrum.Support.finite R k`.
-/
protected def algebraMap : K →+* FiniteAdeleRing R K where
  toFun k := ⟨fun i ↦ k, by
    simp only [Filter.eventually_cofinite, SetLike.mem_coe, mem_adicCompletionIntegers R K,
     adicCompletion, Valued.valuedCompletion_apply, not_le]
    exact HeightOneSpectrum.Support.finite R k⟩
  map_one' := rfl
  map_mul' x y := Subtype.ext <| funext (fun v ↦
    UniformSpace.Completion.coe_mul ((WithVal.equiv (valuation K v)).symm x) y)
  map_zero' := rfl
  map_add' x y := Subtype.ext <| funext (fun v ↦
    UniformSpace.Completion.coe_add ((WithVal.equiv (valuation K v)).symm x) y)

@[simp] theorem algebraMap_apply (k : K) (v : HeightOneSpectrum R) :
    FiniteAdeleRing.algebraMap R K k v = k := rfl

instance : Algebra K (FiniteAdeleRing R K) := (FiniteAdeleRing.algebraMap R K).toAlgebra

instance : Algebra R (FiniteAdeleRing R K) := Algebra.compHom _ (algebraMap R K)

instance : IsScalarTower R K (FiniteAdeleRing R K) :=
  IsScalarTower.of_algebraMap_eq' rfl

variable {R} in
@[ext]
lemma ext {a₁ a₂ : FiniteAdeleRing R K} (h : ∀ v, a₁ v = a₂ v) : a₁ = a₂ :=
  Subtype.ext <| funext h

instance : DFunLike (FiniteAdeleRing R K) (HeightOneSpectrum R) (adicCompletion K) where
  coe a := a.1
  coe_injective' _a _b h := ext K (congrFun h)

section Topology

instance : IsTopologicalRing (FiniteAdeleRing R K) :=
  haveI : Fact (∀ v : HeightOneSpectrum R,
      IsOpen (v.adicCompletionIntegers K : Set (v.adicCompletion K))) :=
    ⟨fun _ ↦ Valued.isOpen_valuationSubring _⟩
  RestrictedProduct.isTopologicalRing (fun (v : HeightOneSpectrum R) ↦ v.adicCompletion K)

end Topology

variable {R K}

def denDivisors (a : FiniteAdeleRing R K) : Set (HeightOneSpectrum R) :=
    {v | a v ∉ v.adicCompletionIntegers K}

theorem denDivisors_finite (a : FiniteAdeleRing R K) : a.denDivisors.Finite := by
  simpa using a.2

theorem notMem_adicCompletionIntegers_at_denDivisors (a : FiniteAdeleRing R K)
      (v : HeightOneSpectrum R) (hv : v ∈ a.denDivisors) :
    a v ∉ v.adicCompletionIntegers K := hv

theorem _root_.Set.diff_nonempty_of_encard_lt_encard {α : Type*} {s t : Set α}
    (h : s.encard < t.encard) : (t \ s).Nonempty := by
  simp [Set.nonempty_iff_ne_empty]
  intro h
  sorry

theorem isUnit_iff_valued_eq_one {v : HeightOneSpectrum R} {a : v.adicCompletionIntegers K} :
    IsUnit a ↔ Valued.v a.1 = 1 := by
  rw [Valuation.Integers.isUnit_iff_valuation_eq_one (F := v.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ))]
  exact .rfl
  apply Valuation.Integers.mk
  · exact FaithfulSMul.algebraMap_injective (↥(adicCompletionIntegers K v)) (adicCompletion K v)
  · simp [mem_adicCompletionIntegers]
  · simp [mem_adicCompletionIntegers]

theorem nonzero_of_isUnit {a : FiniteAdeleRing R K}
    (ha : IsUnit a) :
    ∀ v, a v ≠ 0 := by
  contrapose! ha
  simp [isUnit_iff_exists_inv]
  intro b
  rw [RestrictedProduct.ext_iff]
  simp
  obtain ⟨v, hv⟩ := ha
  use v
  change a v * b v ≠ _
  simp [hv]

theorem isUnit_cofinite_of_isUnit {a : FiniteAdeleRing R K} (ha : IsUnit a) :
    ∀ᶠ v in Filter.cofinite, Valued.v (a v) = 1 := by
  simp
  rw [isUnit_iff_exists_inv] at ha
  obtain ⟨b, hb⟩ := ha
  rw [RestrictedProduct.ext_iff] at hb
  contrapose! hb
  have : (a.denDivisors ∪ b.denDivisors).encard < {v | Valued.v (a v) ≠ 1}.encard := by
    simp [Set.encard_eq_top hb, a.denDivisors_finite, b.denDivisors_finite]
  obtain ⟨v₀, hv₀⟩ := Set.diff_nonempty_of_encard_lt_encard this
  use v₀
  simp at hv₀
  let a' : v₀.adicCompletionIntegers K := ⟨a v₀, by simpa [denDivisors] using hv₀.2.1⟩
  let b' : v₀.adicCompletionIntegers K := ⟨b v₀, by simpa [denDivisors] using hv₀.2.2⟩
  simp
  change a v₀ * b v₀ ≠ 1
  have : ¬IsUnit a' := by rw [isUnit_iff_valued_eq_one]; exact hv₀.1
  rw [isUnit_iff_exists_inv] at this
  simp at this
  have := this (b v₀) (by simpa [denDivisors] using hv₀.2.2)
  simp [a'] at this
  have hi : Function.Injective (algebraMap (v₀.adicCompletionIntegers K) (v₀.adicCompletion K)) := by
    apply FaithfulSMul.algebraMap_injective
  rw [← hi.eq_iff.not] at this
  simp_all

theorem isUnit_of_isUnit_cofinite {a : FiniteAdeleRing R K} (h : ∀ v, a v ≠ 0)
      (ha : ∀ᶠ v in Filter.cofinite, Valued.v (a v) = 1) :
    IsUnit a := by
  rw [isUnit_iff_exists_inv]
  simp at ha
  let S := {v | Valued.v (a v) ≠ 1}
  use .mk (fun v ↦ (a v)⁻¹) (by
    simp
    apply Set.Finite.subset ha
    simp
    intro v hav
    contrapose! hav
    let a' : v.adicCompletionIntegers K := ⟨a v, by simpa [mem_adicCompletionIntegers] using hav.le⟩
    have : Valued.v a'.1 = 1 := by simpa
    change Valued.v a'.1⁻¹ ≤ 1
    rw [map_inv₀, this]
    simp)
  ext v
  change a v * _ = 1
  simp [field, h v]


theorem isUnit_iff {a : FiniteAdeleRing R K} :
    IsUnit a ↔ (∀ v, a v ≠ 0) ∧ ∀ᶠ v in Filter.cofinite, Valued.v (a v) = 1 := by
  refine ⟨fun h ↦ ⟨nonzero_of_isUnit h, isUnit_cofinite_of_isUnit h⟩,
    fun h ↦ isUnit_of_isUnit_cofinite h.1 h.2⟩

variable (R K) in
def unitEmbedding : Kˣ →* (FiniteAdeleRing R K)ˣ := Units.map (algebraMap K (FiniteAdeleRing R K))

@[simp] theorem unitEmbedding_apply (k : Kˣ) :
    unitEmbedding R K k = algebraMap K (FiniteAdeleRing R K) k := rfl

instance : Coe Kˣ (FiniteAdeleRing R K)ˣ where
  coe x := Units.map (algebraMap K (FiniteAdeleRing R K)) x

end FiniteAdeleRing

end IsDedekindDomain
