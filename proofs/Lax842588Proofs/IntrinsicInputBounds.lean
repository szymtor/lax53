import Lax842588Proofs.IntrinsicParameterEncoding
import Lax842588Proofs.AutomatonRamArenaBounds

/-! Mathematical size and payload bounds for the unchanged uniform input arena. -/

namespace Lax842588Proofs.IntrinsicInputBounds

open Lax146103.MSOSyntax Lax842588.RankedTree Lax842588.TreeStructure Lax842588.ValueTranslations
open Lax842588.StructuralRepresentations Lax842588.MSOLinearTime
open Lax842588.TreeModelCheckingEncoding (treeSize)
open Lax560851.StructuralPresentation Lax560851.StructuralCombinators Lax560851.WordArena
open Lax842588Proofs.ArenaSemantics Lax842588Proofs.IntrinsicParameterEncoding

theorem input_size_eq (alphabet : RankedAlphabetCode)
    (φ : Sentence (treeSignature alphabet.toRankedAlphabet))
    (t : Tree alphabet.toRankedAlphabet) :
    inputStructuralSize alphabet φ t =
      (derivedPresentation : Presentation RankedAlphabetCode).structuralSize alphabet +
        sentenceSize alphabet φ + (treeStructure alphabet t).nodes + 6 := by
  simp only [inputStructuralSize, msoTreeRaw, Raw.constructor, Raw.fields, Raw.nodes,
    Presentation.structuralSize, sentenceSize]
  omega

theorem tree_size_le_input (alphabet : RankedAlphabetCode)
    (φ : Sentence (treeSignature alphabet.toRankedAlphabet))
    (t : Tree alphabet.toRankedAlphabet) : treeSize t ≤ inputStructuralSize alphabet φ t := by
  rw [input_size_eq]
  have := AutomatonRamArenaBounds.treeSize_le_treeStructure_nodes alphabet t
  omega

theorem input_size_le (alphabet : RankedAlphabetCode)
    (φ : Sentence (treeSignature alphabet.toRankedAlphabet))
    (t : Tree alphabet.toRankedAlphabet) :
    inputStructuralSize alphabet φ t ≤ (parameterSize alphabet φ + 6) * (treeSize t + 1) := by
  have ht := AutomatonRamArenaBounds.treeStructure_nodes_add_one alphabet t
  have hp : (derivedPresentation : Presentation RankedAlphabetCode).structuralSize alphabet +
      sentenceSize alphabet φ ≤ parameterSize alphabet φ := by unfold parameterSize; omega
  have hs : inputStructuralSize alphabet φ t ≤ parameterSize alphabet φ + 6 * treeSize t + 6 := by
    rw [input_size_eq]
    omega
  nlinarith [Nat.zero_le (parameterSize alphabet φ * treeSize t)]

theorem arena_memory (alphabet : RankedAlphabetCode)
    (φ : Sentence (treeSignature alphabet.toRankedAlphabet))
    (t : Tree alphabet.toRankedAlphabet) :
    (encodeRaw (msoTreeRaw alphabet φ t)).memoryWords = 3 * inputStructuralSize alphabet φ t :=
  Lax560851Proofs.WordArena.encodeRaw_memoryWords_proof _

theorem arena_values_lt (B : Nat) (alphabet : RankedAlphabetCode)
    (φ : Sentence (treeSignature alphabet.toRankedAlphabet))
    (t : Tree alphabet.toRankedAlphabet)
    (hpayload : inputPayloadMax alphabet φ t < B)
    (hspace : 3 * inputStructuralSize alphabet φ t ≤ B) :
    ∀ v ∈ arenaWords (encodeRaw (msoTreeRaw alphabet φ t)), v < B := by
  intro v hv
  apply Lax560851Proofs.WordArena.encodeRaw_toInput_lt (msoTreeRaw alphabet φ t) B hpayload hspace
  exact List.mem_cons_of_mem _ hv

end Lax842588Proofs.IntrinsicInputBounds
