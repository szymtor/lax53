import Lax53Proofs.EncodedPrimitiveAtomicAutomata

namespace Lax53Proofs.EncodedPrimitiveProjection

open Lax53.EffectiveTranslations
open Lax53Proofs.MarkedAlphabetEncoding
open Lax53Proofs.EncodedPrimitiveAtomicAutomata
open Lax53Proofs.EncodedProjection
open Lax53Proofs.MarkedTrees

/-- Numeric test saying that `source` becomes `target` after forgetting the
newest first-order marker. -/
def dropFOMatches (n m source target : Nat) : Bool :=
  decide (baseSymbol (n + 1) m source = baseSymbol n m target) &&
    ((List.range n).all fun x =>
      foMarked (n + 1) m source (x + 1) == foMarked n m target x) &&
    ((List.range m).all fun X =>
      soMarked m source X == soMarked m target X)

/-- Numeric test saying that `source` becomes `target` after forgetting the
newest monadic marker. -/
def dropSOMatches (n m source target : Nat) : Bool :=
  decide (baseSymbol n (m + 1) source = baseSymbol n m target) &&
    ((List.range n).all fun x =>
      foMarked n (m + 1) source x == foMarked n m target x) &&
    ((List.range m).all fun X =>
      soMarked (m + 1) source (X + 1) == soMarked m target X)

/-- The complete numeric fiber of a target marked symbol under first-order
marker projection. -/
def dropFOOfP (alphabet : RankedAlphabetCode) (n m target : Nat) : List Nat :=
  (List.range (symbolCount alphabet (n + 1) m)).filter fun source =>
    dropFOMatches n m source target

/-- The complete numeric fiber of a target marked symbol under monadic-marker
projection. -/
def dropSOOfP (alphabet : RankedAlphabetCode) (n m target : Nat) : List Nat :=
  (List.range (symbolCount alphabet n (m + 1))).filter fun source =>
    dropSOMatches n m source target

theorem dropFOMatches_prim : Primrec fun p : Nat × Nat × Nat × Nat =>
    dropFOMatches p.1 p.2.1 p.2.2.1 p.2.2.2 := by
  let P := Nat × Nat × Nat × Nat
  have hbase : Primrec fun p : P => decide
      (baseSymbol (p.1 + 1) p.2.1 p.2.2.1 =
        baseSymbol p.1 p.2.1 p.2.2.2) := by
    exact (Primrec.eq.comp
      (baseSymbol_prim.comp <| Primrec.pair
        (Primrec.succ.comp Primrec.fst) <|
          Primrec.pair (Primrec.fst.comp Primrec.snd)
            (Primrec.fst.comp <| Primrec.snd.comp Primrec.snd))
      (baseSymbol_prim.comp <| Primrec.pair Primrec.fst <|
        Primrec.pair (Primrec.fst.comp Primrec.snd)
          (Primrec.snd.comp <| Primrec.snd.comp Primrec.snd))).decide
  have hfo : Primrec fun p : P => (List.range p.1).all fun x =>
      foMarked (p.1 + 1) p.2.1 p.2.2.1 (x + 1) ==
        foMarked p.1 p.2.1 p.2.2.2 x := by
    apply listAll_prim (fun p : P => List.range p.1)
      (fun p x => foMarked (p.1 + 1) p.2.1 p.2.2.1 (x + 1) ==
        foMarked p.1 p.2.1 p.2.2.2 x)
      (Primrec.list_range.comp Primrec.fst)
    exact Primrec.beq.comp
      (foMarked_prim.comp <| Primrec.pair
        (Primrec.succ.comp <| Primrec.fst.comp Primrec.fst) <|
          Primrec.pair (Primrec.fst.comp <| Primrec.snd.comp Primrec.fst) <|
            Primrec.pair
              (Primrec.fst.comp <| Primrec.snd.comp <| Primrec.snd.comp Primrec.fst)
              (Primrec.succ.comp Primrec.snd))
      (foMarked_prim.comp <| Primrec.pair
        (Primrec.fst.comp Primrec.fst) <|
          Primrec.pair (Primrec.fst.comp <| Primrec.snd.comp Primrec.fst) <|
            Primrec.pair
              (Primrec.snd.comp <| Primrec.snd.comp <| Primrec.snd.comp Primrec.fst)
              Primrec.snd)
  have hso : Primrec fun p : P => (List.range p.2.1).all fun X =>
      soMarked p.2.1 p.2.2.1 X == soMarked p.2.1 p.2.2.2 X := by
    apply listAll_prim (fun p : P => List.range p.2.1)
      (fun p X => soMarked p.2.1 p.2.2.1 X == soMarked p.2.1 p.2.2.2 X)
      (Primrec.list_range.comp <| Primrec.fst.comp Primrec.snd)
    exact Primrec.beq.comp
      (soMarked_prim.comp <| Primrec.pair
        (Primrec.fst.comp <| Primrec.snd.comp Primrec.fst) <|
          Primrec.pair
            (Primrec.fst.comp <| Primrec.snd.comp <| Primrec.snd.comp Primrec.fst)
            Primrec.snd)
      (soMarked_prim.comp <| Primrec.pair
        (Primrec.fst.comp <| Primrec.snd.comp Primrec.fst) <|
          Primrec.pair
            (Primrec.snd.comp <| Primrec.snd.comp <| Primrec.snd.comp Primrec.fst)
            Primrec.snd)
  unfold dropFOMatches
  exact Primrec.and.comp (Primrec.and.comp hbase hfo) hso

theorem dropSOMatches_prim : Primrec fun p : Nat × Nat × Nat × Nat =>
    dropSOMatches p.1 p.2.1 p.2.2.1 p.2.2.2 := by
  let P := Nat × Nat × Nat × Nat
  have hbase : Primrec fun p : P => decide
      (baseSymbol p.1 (p.2.1 + 1) p.2.2.1 =
        baseSymbol p.1 p.2.1 p.2.2.2) := by
    exact (Primrec.eq.comp
      (baseSymbol_prim.comp <| Primrec.pair Primrec.fst <|
        Primrec.pair (Primrec.succ.comp <| Primrec.fst.comp Primrec.snd)
          (Primrec.fst.comp <| Primrec.snd.comp Primrec.snd))
      (baseSymbol_prim.comp <| Primrec.pair Primrec.fst <|
        Primrec.pair (Primrec.fst.comp Primrec.snd)
          (Primrec.snd.comp <| Primrec.snd.comp Primrec.snd))).decide
  have hfo : Primrec fun p : P => (List.range p.1).all fun x =>
      foMarked p.1 (p.2.1 + 1) p.2.2.1 x ==
        foMarked p.1 p.2.1 p.2.2.2 x := by
    apply listAll_prim (fun p : P => List.range p.1)
      (fun p x => foMarked p.1 (p.2.1 + 1) p.2.2.1 x ==
        foMarked p.1 p.2.1 p.2.2.2 x)
      (Primrec.list_range.comp Primrec.fst)
    exact Primrec.beq.comp
      (foMarked_prim.comp <| Primrec.pair (Primrec.fst.comp Primrec.fst) <|
        Primrec.pair
          (Primrec.succ.comp <| Primrec.fst.comp <| Primrec.snd.comp Primrec.fst) <|
          Primrec.pair
            (Primrec.fst.comp <| Primrec.snd.comp <| Primrec.snd.comp Primrec.fst)
            Primrec.snd)
      (foMarked_prim.comp <| Primrec.pair (Primrec.fst.comp Primrec.fst) <|
        Primrec.pair (Primrec.fst.comp <| Primrec.snd.comp Primrec.fst) <|
          Primrec.pair
            (Primrec.snd.comp <| Primrec.snd.comp <| Primrec.snd.comp Primrec.fst)
            Primrec.snd)
  have hso : Primrec fun p : P => (List.range p.2.1).all fun X =>
      soMarked (p.2.1 + 1) p.2.2.1 (X + 1) ==
        soMarked p.2.1 p.2.2.2 X := by
    apply listAll_prim (fun p : P => List.range p.2.1)
      (fun p X => soMarked (p.2.1 + 1) p.2.2.1 (X + 1) ==
        soMarked p.2.1 p.2.2.2 X)
      (Primrec.list_range.comp <| Primrec.fst.comp Primrec.snd)
    exact Primrec.beq.comp
      (soMarked_prim.comp <| Primrec.pair
        (Primrec.succ.comp <| Primrec.fst.comp <| Primrec.snd.comp Primrec.fst) <|
          Primrec.pair
            (Primrec.fst.comp <| Primrec.snd.comp <| Primrec.snd.comp Primrec.fst)
            (Primrec.succ.comp Primrec.snd))
      (soMarked_prim.comp <| Primrec.pair
        (Primrec.fst.comp <| Primrec.snd.comp Primrec.fst) <|
          Primrec.pair
            (Primrec.snd.comp <| Primrec.snd.comp <| Primrec.snd.comp Primrec.fst)
            Primrec.snd)
  unfold dropSOMatches
  exact Primrec.and.comp (Primrec.and.comp hbase hfo) hso

theorem dropFOOfP_prim : Primrec fun p : RankedAlphabetCode × Nat × Nat × Nat =>
    dropFOOfP p.1 p.2.1 p.2.2.1 p.2.2.2 := by
  unfold dropFOOfP
  have hsource : Primrec fun p : RankedAlphabetCode × Nat × Nat × Nat =>
      List.range (symbolCount p.1 (p.2.1 + 1) p.2.2.1) :=
    Primrec.list_range.comp <| symbolCount_prim.comp <|
      Primrec.pair Primrec.fst <| Primrec.pair
        (Primrec.succ.comp <| Primrec.fst.comp Primrec.snd)
        (Primrec.fst.comp <| Primrec.snd.comp Primrec.snd)
  have hrel : PrimrecRel fun (source : Nat)
      (p : RankedAlphabetCode × Nat × Nat × Nat) =>
      dropFOMatches p.2.1 p.2.2.1 source p.2.2.2 = true :=
    (Primrec.eq.comp
      (dropFOMatches_prim.comp <| Primrec.pair
        (Primrec.fst.comp <| Primrec.snd.comp Primrec.snd) <| Primrec.pair
          (Primrec.fst.comp <| Primrec.snd.comp <| Primrec.snd.comp Primrec.snd) <|
          Primrec.pair Primrec.fst
            (Primrec.snd.comp <| Primrec.snd.comp <| Primrec.snd.comp Primrec.snd))
      (Primrec.const true)).primrecRel
  exact hrel.listFilter.comp hsource Primrec.id
    |>.of_eq fun p => by apply List.filter_congr; simp

theorem dropSOOfP_prim : Primrec fun p : RankedAlphabetCode × Nat × Nat × Nat =>
    dropSOOfP p.1 p.2.1 p.2.2.1 p.2.2.2 := by
  unfold dropSOOfP
  have hsource : Primrec fun p : RankedAlphabetCode × Nat × Nat × Nat =>
      List.range (symbolCount p.1 p.2.1 (p.2.2.1 + 1)) :=
    Primrec.list_range.comp <| symbolCount_prim.comp <|
      Primrec.pair Primrec.fst <| Primrec.pair
        (Primrec.fst.comp Primrec.snd)
        (Primrec.succ.comp <| Primrec.fst.comp <| Primrec.snd.comp Primrec.snd)
  have hrel : PrimrecRel fun (source : Nat)
      (p : RankedAlphabetCode × Nat × Nat × Nat) =>
      dropSOMatches p.2.1 p.2.2.1 source p.2.2.2 = true :=
    (Primrec.eq.comp
      (dropSOMatches_prim.comp <| Primrec.pair
        (Primrec.fst.comp <| Primrec.snd.comp Primrec.snd) <| Primrec.pair
          (Primrec.fst.comp <| Primrec.snd.comp <| Primrec.snd.comp Primrec.snd) <|
          Primrec.pair Primrec.fst
            (Primrec.snd.comp <| Primrec.snd.comp <| Primrec.snd.comp Primrec.snd))
      (Primrec.const true)).primrecRel
  exact hrel.listFilter.comp hsource Primrec.id
    |>.of_eq fun p => by apply List.filter_congr; simp

theorem dropFOMatches_iff (alphabet : RankedAlphabetCode) (n m : Nat)
    (source : (code alphabet (n + 1) m).toRankedAlphabet.Symbol)
    (target : (code alphabet n m).toRankedAlphabet.Symbol) :
    dropFOMatches n m source.val target.val = true ↔
      dropFOMap alphabet n m source = target := by
  constructor
  · intro h
    simp only [dropFOMatches, Bool.and_eq_true, decide_eq_true_eq,
      List.all_eq_true, beq_iff_eq] at h
    rcases h with ⟨⟨hbase, hfo⟩, hso⟩
    rw [← to_from alphabet n m target]
    change toCodeSymbol alphabet n m
        (MarkedAlphabet.dropFO (fromCodeSymbol alphabet (n + 1) m source)) =
      toCodeSymbol alphabet n m (fromCodeSymbol alphabet n m target)
    apply congrArg (toCodeSymbol alphabet n m)
    change MarkedAlphabet.dropFO (fromCodeSymbol alphabet (n + 1) m source) =
      fromCodeSymbol alphabet n m target
    apply Prod.ext
    · apply Fin.ext
      simpa [MarkedAlphabet.dropFO, fromCode_base] using hbase
    · apply Prod.ext
      · funext x
        have hx := hfo x.val (List.mem_range.mpr x.isLt)
        simpa [MarkedAlphabet.dropFO, fromCode_fo] using hx
      · funext X
        have hX := hso X.val (List.mem_range.mpr X.isLt)
        simpa [MarkedAlphabet.dropFO, fromCode_so] using hX
  · intro h
    have hs : MarkedAlphabet.dropFO
        (fromCodeSymbol alphabet (n + 1) m source) =
        fromCodeSymbol alphabet n m target := by
      have := congrArg (fromCodeSymbol alphabet n m) h
      simpa [dropFOMap, from_to, to_from] using this
    simp only [dropFOMatches, Bool.and_eq_true, decide_eq_true_eq,
      List.all_eq_true, beq_iff_eq]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · have := congrArg (fun s => s.1.val) hs
      simpa [MarkedAlphabet.dropFO, fromCode_base] using this
    · intro x hx
      let i : Fin n := ⟨x, List.mem_range.mp hx⟩
      have := congrArg (fun s => s.2.1 i) hs
      simpa [i, MarkedAlphabet.dropFO, fromCode_fo] using this
    · intro X hX
      let I : Fin m := ⟨X, List.mem_range.mp hX⟩
      have := congrArg (fun s => s.2.2 I) hs
      simpa [I, MarkedAlphabet.dropFO, fromCode_so] using this

theorem dropSOMatches_iff (alphabet : RankedAlphabetCode) (n m : Nat)
    (source : (code alphabet n (m + 1)).toRankedAlphabet.Symbol)
    (target : (code alphabet n m).toRankedAlphabet.Symbol) :
    dropSOMatches n m source.val target.val = true ↔
      dropSOMap alphabet n m source = target := by
  constructor
  · intro h
    simp only [dropSOMatches, Bool.and_eq_true, decide_eq_true_eq,
      List.all_eq_true, beq_iff_eq] at h
    rcases h with ⟨⟨hbase, hfo⟩, hso⟩
    rw [← to_from alphabet n m target]
    change toCodeSymbol alphabet n m
        (MarkedAlphabet.dropSO (fromCodeSymbol alphabet n (m + 1) source)) =
      toCodeSymbol alphabet n m (fromCodeSymbol alphabet n m target)
    apply congrArg (toCodeSymbol alphabet n m)
    change MarkedAlphabet.dropSO (fromCodeSymbol alphabet n (m + 1) source) =
      fromCodeSymbol alphabet n m target
    apply Prod.ext
    · apply Fin.ext
      simpa [MarkedAlphabet.dropSO, fromCode_base] using hbase
    · apply Prod.ext
      · funext x
        have hx := hfo x.val (List.mem_range.mpr x.isLt)
        simpa [MarkedAlphabet.dropSO, fromCode_fo] using hx
      · funext X
        have hX := hso X.val (List.mem_range.mpr X.isLt)
        simpa [MarkedAlphabet.dropSO, fromCode_so] using hX
  · intro h
    have hs : MarkedAlphabet.dropSO
        (fromCodeSymbol alphabet n (m + 1) source) =
        fromCodeSymbol alphabet n m target := by
      have := congrArg (fromCodeSymbol alphabet n m) h
      simpa [dropSOMap, from_to, to_from] using this
    simp only [dropSOMatches, Bool.and_eq_true, decide_eq_true_eq,
      List.all_eq_true, beq_iff_eq]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · have := congrArg (fun s => s.1.val) hs
      simpa [MarkedAlphabet.dropSO, fromCode_base] using this
    · intro x hx
      let i : Fin n := ⟨x, List.mem_range.mp hx⟩
      have := congrArg (fun s => s.2.1 i) hs
      simpa [i, MarkedAlphabet.dropSO, fromCode_fo] using this
    · intro X hX
      let I : Fin m := ⟨X, List.mem_range.mp hX⟩
      have := congrArg (fun s => s.2.2 I) hs
      simpa [I, MarkedAlphabet.dropSO, fromCode_so] using this

theorem mem_dropFOOfP (alphabet : RankedAlphabetCode) (n m : Nat)
    (source : (code alphabet (n + 1) m).toRankedAlphabet.Symbol) :
    source.val ∈ dropFOOfP alphabet n m (dropFOMap alphabet n m source).val := by
  simp only [dropFOOfP, List.mem_filter, List.mem_range]
  exact ⟨by simpa [code_length] using source.isLt,
    (dropFOMatches_iff alphabet n m source (dropFOMap alphabet n m source)).mpr rfl⟩

theorem mem_dropSOOfP (alphabet : RankedAlphabetCode) (n m : Nat)
    (source : (code alphabet n (m + 1)).toRankedAlphabet.Symbol) :
    source.val ∈ dropSOOfP alphabet n m (dropSOMap alphabet n m source).val := by
  simp only [dropSOOfP, List.mem_filter, List.mem_range]
  exact ⟨by simpa [code_length] using source.isLt,
    (dropSOMatches_iff alphabet n m source (dropSOMap alphabet n m source)).mpr rfl⟩

theorem complete_dropFOOfP (alphabet : RankedAlphabetCode) (n m : Nat) :
    CompleteFibers (code alphabet (n + 1) m) (code alphabet n m)
      (dropFOMap alphabet n m) (dropFOOfP alphabet n m) := by
  intro target source hsource
  simp only [dropFOOfP, List.mem_filter, List.mem_range] at hsource
  rcases hsource with ⟨hbound, hmatch⟩
  let s : (code alphabet (n + 1) m).toRankedAlphabet.Symbol :=
    ⟨source, by simpa [code_length] using hbound⟩
  exact ⟨s, rfl, (dropFOMatches_iff alphabet n m s target).mp hmatch⟩

theorem complete_dropSOOfP (alphabet : RankedAlphabetCode) (n m : Nat) :
    CompleteFibers (code alphabet n (m + 1)) (code alphabet n m)
      (dropSOMap alphabet n m) (dropSOOfP alphabet n m) := by
  intro target source hsource
  simp only [dropSOOfP, List.mem_filter, List.mem_range] at hsource
  rcases hsource with ⟨hbound, hmatch⟩
  let s : (code alphabet n (m + 1)).toRankedAlphabet.Symbol :=
    ⟨source, by simpa [code_length] using hbound⟩
  exact ⟨s, rfl, (dropSOMatches_iff alphabet n m s target).mp hmatch⟩

end Lax53Proofs.EncodedPrimitiveProjection
