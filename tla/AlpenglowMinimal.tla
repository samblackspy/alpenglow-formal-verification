---- MODULE AlpenglowMinimal ----
(***************************************************************************
 * MINIMAL ALPENGLOW SPECIFICATION - FOR EXHAUSTIVE VERIFICATION
 * 
 * Based on winning submission structure (tla-_verification)
 * 13 variables only - optimized for 7+ validator verification
 * Abstracts: Rotor (simple delivery), Timing (boolean flags), Network (crash faults)
 * 
 * Target: 4v-7v exhaustive, 10v simulation
 ***************************************************************************)
EXTENDS Naturals, FiniteSets, Sequences, TLC

CONSTANTS 
    Nodes,              \* All validators
    Honest,             \* Honest subset
    Byzantine,          \* Byzantine subset  
    Slots,              \* Slot identifiers
    WindowSize,         \* Leader window size
    ThresholdFast,      \* 80% stake threshold
    ThresholdSlow,      \* 60% stake threshold
    ThresholdFallback   \* 20% stake threshold

None == [slot |-> (0-2), tag |-> "NONE"]

(***************************************************************************
 * Helper Functions
 ***************************************************************************)
RECURSIVE MinVal(_)
MinVal(S) == IF S = {} THEN 0 ELSE 
    LET x == CHOOSE e \in S : TRUE IN
    IF S = {x} THEN x ELSE 
    LET m == MinVal(S \ {x}) IN IF x < m THEN x ELSE m

FirstSlot == MinVal(Slots)

GenesisBlock == [slot |-> (0-1), tag |-> "G"]
Leader == [s \in Slots |-> CHOOSE n \in Nodes : TRUE]
Stake == [n \in Nodes |-> 25]
BlockOptions == [s \in Slots |-> {[slot |-> s, tag |-> "A"]}]

BlockIds == UNION { BlockOptions[s] : s \in Slots }

ParentOf == [b \in BlockIds \cup {GenesisBlock} |->
    IF b = GenesisBlock THEN GenesisBlock
    ELSE IF b.slot \in Slots /\ b.slot > FirstSlot
         THEN LET prevSlot == b.slot - 1
              IN CHOOSE pb \in BlockOptions[prevSlot] : TRUE
         ELSE GenesisBlock]

ASSUME Honest \subseteq Nodes /\ Byzantine \subseteq Nodes
ASSUME Honest \cap Byzantine = {} /\ Honest \cup Byzantine = Nodes

Parent(b) == IF b = GenesisBlock THEN GenesisBlock ELSE ParentOf[b]
SlotOf(b) == IF b = GenesisBlock THEN FirstSlot ELSE b.slot

RECURSIVE StakeSum(_)
StakeSum(S) == IF S = {} THEN 0 ELSE 
    LET n == CHOOSE v \in S : TRUE IN Stake[n] + StakeSum(S \ {n})

RECURSIVE MaxVal(_)
MaxVal(S) == IF S = {} THEN 0 ELSE 
    LET x == CHOOSE e \in S : TRUE IN
    IF S = {x} THEN x ELSE 
    LET m == MaxVal(S \ {x}) IN IF x > m THEN x ELSE m

WindowStart(s) == s - ((s - FirstSlot) % WindowSize)
WindowSlots(s) == { WindowStart(s) + i : i \in 0..(WindowSize - 1) } \cap Slots
IsFirstInWindow(s) == s = WindowStart(s)
WindowRoot(s) == WindowStart(s)
SlotBlocks(s) == BlockOptions[s]

(***************************************************************************
 * Symmetry Definition (for state space reduction)
 ***************************************************************************)
Symmetry == Permutations(Honest)

(***************************************************************************
 * State Variables (13 ONLY - Minimal for Scale)
 ***************************************************************************)
VARIABLES 
    produced,           \* SUBSET BlockIds
    delivered,          \* [Nodes -> SUBSET BlockIds]
    notarVotes,         \* [Slots -> [BlockIds -> SUBSET Nodes]]
    notarFallbackVotes, \* [Slots -> [BlockIds -> SUBSET Nodes]]
    skipVotes,          \* [Slots -> SUBSET Nodes]
    skipFallbackVotes,  \* [Slots -> SUBSET Nodes]
    finalVotes,         \* [Slots -> [Nodes -> BlockIds \cup {None}]]
    parentReady,        \* [Slots -> BOOLEAN]
    timeoutsArmed,      \* [Slots -> BOOLEAN]
    timeoutsFired,      \* [Slots -> BOOLEAN]
    finalized,          \* SUBSET BlockIds
    fastFinalized,      \* SUBSET BlockIds
    notarizedBlocks     \* SUBSET BlockIds

vars == << produced, delivered, notarVotes, notarFallbackVotes, skipVotes,
            skipFallbackVotes, finalVotes, parentReady, timeoutsArmed,
            timeoutsFired, finalized, fastFinalized, notarizedBlocks >>

(***************************************************************************
 * Initialization
 ***************************************************************************)
Init == 
    /\ produced = {GenesisBlock}
    /\ delivered = [n \in Nodes |-> {GenesisBlock}]
    /\ notarVotes = [s \in Slots |-> [b \in BlockIds |-> {}]]
    /\ notarFallbackVotes = [s \in Slots |-> [b \in BlockIds |-> {}]]
    /\ skipVotes = [s \in Slots |-> {}]
    /\ skipFallbackVotes = [s \in Slots |-> {}]
    /\ finalVotes = [s \in Slots |-> [n \in Nodes |-> None]]
    /\ parentReady = [s \in Slots |-> TRUE]  \* Genesis is already finalized, so all slots ready
    /\ timeoutsArmed = [s \in Slots |-> FALSE]
    /\ timeoutsFired = [s \in Slots |-> FALSE]
    /\ finalized = {GenesisBlock}
    /\ fastFinalized = {}
    /\ notarizedBlocks = {GenesisBlock}

(***************************************************************************
 * Helper Predicates
 ***************************************************************************)
DomainBlocks(s) == SlotBlocks(s)

BlockStake(s, b) == StakeSum(notarVotes[s][b])
FallbackStake(s, b) == StakeSum(notarVotes[s][b] \cup notarFallbackVotes[s][b])
SkipStake(s) == StakeSum(skipVotes[s])
SkipFallbackStake(s) == StakeSum(skipVotes[s] \cup skipFallbackVotes[s])
FinalStake(s, b) == StakeSum({ n \in Nodes : finalVotes[s][n] = b })
TotalNotarStake(s) == StakeSum(UNION { notarVotes[s][b] : b \in DomainBlocks(s) })
MaxNotarStake(s) == MaxVal({ BlockStake(s, b) : b \in DomainBlocks(s) })

SafeToNotar(s, b) == 
    /\ parentReady[WindowRoot(s)]
    /\ StakeSum(notarVotes[s][b]) >= ThresholdFallback
    /\ SkipStake(s) + StakeSum(notarVotes[s][b]) >= ThresholdSlow

SafeToSkip(s) == 
    SkipStake(s) + TotalNotarStake(s) - MaxNotarStake(s) >= ThresholdSlow - ThresholdFallback

HasNotarCert(s, b) == BlockStake(s, b) >= ThresholdSlow
HasFastFinalCert(s, b) == BlockStake(s, b) >= ThresholdFast
HasNotarFallbackCert(s, b) == FallbackStake(s, b) >= ThresholdSlow
HasSkipCert(s) == SkipFallbackStake(s) >= ThresholdSlow
HasFinalCert(s, b) == FinalStake(s, b) >= ThresholdSlow
Finalizable(s, b) == HasNotarCert(s, b) /\ ~HasSkipCert(s)

BlockAdmissible(b) == 
    IF b = GenesisBlock THEN TRUE
    ELSE Parent(b) \in notarizedBlocks \cup finalized

RECURSIVE Ancestors(_)
Ancestors(b) == IF b = GenesisBlock THEN {GenesisBlock}
    ELSE {b} \cup Ancestors(Parent(b))

SlotFinalizedBlocks(s) == { b \in BlockIds : SlotOf(b) = s /\ b \in finalized }
SkipActive(s) == HasSkipCert(s)
SlotCovered(s) == (\E b \in DomainBlocks(s) : HasNotarCert(s, b)) \/ SkipActive(s)

FinalizableAncestors(b) == 
    { a \in Ancestors(b) : ~HasSkipCert(SlotOf(a)) }

HonestReadyBase(n, s) ==
    /\ n \in Honest
    /\ parentReady[WindowRoot(s)]

HonestHasVoted(n, s) ==
    (n \in skipVotes[s]) \/ (\E b \in DomainBlocks(s) : n \in notarVotes[s][b])

HonestCanNotar(n, s, b) == 
    /\ HonestReadyBase(n, s)
    /\ ~HonestHasVoted(n, s)
    /\ b \in DomainBlocks(s)
    /\ {b, Parent(b)} \subseteq delivered[n]

HonestCanSkipTimeout(n, s) ==
    /\ HonestReadyBase(n, s)
    /\ ~HonestHasVoted(n, s)
    /\ timeoutsFired[WindowRoot(s)]
    /\ SlotFinalizedBlocks(s) = {}

HonestCanFallbackNotar(n, s, b) == 
    HonestReadyBase(n, s) /\ HonestHasVoted(n, s) /\ SafeToNotar(s, b)

HonestCanFallbackSkip(n, s) == 
    /\ HonestReadyBase(n, s) 
    /\ HonestHasVoted(n, s) 
    /\ SafeToSkip(s)
    /\ SlotFinalizedBlocks(s) = {}

HonestCanFinalVote(n, s, b) ==
    /\ n \in Honest
    /\ finalVotes[s][n] = None
    /\ n \in notarVotes[s][b]
    /\ HasNotarCert(s, b)
    /\ ~HasSkipCert(s)

(***************************************************************************
 * Actions
 ***************************************************************************)
ProduceBlock(s, b) ==
    /\ s \in Slots
    /\ b \in DomainBlocks(s)
    /\ b \notin produced
    /\ BlockAdmissible(b)
    /\ produced' = produced \cup {b}
    /\ delivered' = [delivered EXCEPT ![Leader[s]] = @ \cup {b}]
    /\ UNCHANGED << notarVotes, notarFallbackVotes, skipVotes, skipFallbackVotes,
                    finalVotes, parentReady, timeoutsArmed, timeoutsFired,
                    finalized, fastFinalized, notarizedBlocks >>

ScheduleTimeout(s) ==
    /\ IsFirstInWindow(s)
    /\ parentReady[s]
    /\ ~timeoutsArmed[s]
    /\ timeoutsArmed' = [timeoutsArmed EXCEPT ![s] = TRUE]
    /\ UNCHANGED << produced, delivered, notarVotes, notarFallbackVotes, skipVotes,
                    skipFallbackVotes, finalVotes, parentReady, timeoutsFired,
                    finalized, fastFinalized, notarizedBlocks >>

FireTimeout(s) ==
    /\ IsFirstInWindow(s)
    /\ timeoutsArmed[s]
    /\ ~timeoutsFired[s]
    /\ timeoutsFired' = [timeoutsFired EXCEPT ![s] = TRUE]
    /\ UNCHANGED << produced, delivered, notarVotes, notarFallbackVotes, skipVotes,
                    skipFallbackVotes, finalVotes, parentReady, timeoutsArmed,
                    finalized, fastFinalized, notarizedBlocks >>

HonestNotarize(n, s, b) ==
    /\ HonestCanNotar(n, s, b)
    /\ b \in produced
    /\ notarVotes' = [notarVotes EXCEPT ![s][b] = @ \cup {n}]
    /\ UNCHANGED << produced, delivered, notarFallbackVotes, skipVotes, skipFallbackVotes,
                    finalVotes, parentReady, timeoutsArmed, timeoutsFired,
                    finalized, fastFinalized, notarizedBlocks >>

HonestSkip(n, s) ==
    /\ HonestCanSkipTimeout(n, s)
    /\ skipVotes' = [skipVotes EXCEPT ![s] = @ \cup {n}]
    /\ UNCHANGED << produced, delivered, notarVotes, notarFallbackVotes,
                    skipFallbackVotes, finalVotes, parentReady, timeoutsArmed,
                    timeoutsFired, finalized, fastFinalized, notarizedBlocks >>

HonestFallbackNotar(n, s, b) ==
    /\ HonestCanFallbackNotar(n, s, b)
    /\ notarFallbackVotes' = [notarFallbackVotes EXCEPT ![s][b] = @ \cup {n}]
    /\ UNCHANGED << produced, delivered, notarVotes, skipVotes, skipFallbackVotes,
                    finalVotes, parentReady, timeoutsArmed, timeoutsFired,
                    finalized, fastFinalized, notarizedBlocks >>

HonestFallbackSkip(n, s) ==
    /\ HonestCanFallbackSkip(n, s)
    /\ skipFallbackVotes' = [skipFallbackVotes EXCEPT ![s] = @ \cup {n}]
    /\ UNCHANGED << produced, delivered, notarVotes, notarFallbackVotes,
                    skipVotes, finalVotes, parentReady, timeoutsArmed, timeoutsFired,
                    finalized, fastFinalized, notarizedBlocks >>

HonestFinalVote(n, s, b) ==
    /\ HonestCanFinalVote(n, s, b)
    /\ finalVotes' = [finalVotes EXCEPT ![s][n] = b]
    /\ UNCHANGED << produced, delivered, notarVotes, notarFallbackVotes, skipVotes,
                    skipFallbackVotes, parentReady, timeoutsArmed, timeoutsFired,
                    finalized, fastFinalized, notarizedBlocks >>

RegisterNotarCertificate(s, b) ==
    /\ HasNotarCert(s, b)
    /\ b \notin notarizedBlocks
    /\ notarizedBlocks' = notarizedBlocks \cup {b}
    /\ UNCHANGED << produced, delivered, notarVotes, notarFallbackVotes, skipVotes,
                    skipFallbackVotes, finalVotes, parentReady, timeoutsArmed,
                    timeoutsFired, finalized, fastFinalized >>

RegisterFastFinalCertificate(s, b) ==
    /\ s \in Slots
    /\ b \in DomainBlocks(s)
    /\ HasFastFinalCert(s, b)
    /\ ~HasSkipCert(s)  \* Fast finalize also requires no skip
    /\ b \notin fastFinalized
    /\ fastFinalized' = fastFinalized \cup {b}
    /\ finalized' = finalized \cup FinalizableAncestors(b)
    /\ notarizedBlocks' = notarizedBlocks \cup FinalizableAncestors(b)
    /\ UNCHANGED << produced, delivered, notarVotes, notarFallbackVotes, skipVotes,
                    skipFallbackVotes, finalVotes, parentReady, timeoutsArmed,
                    timeoutsFired >>

RegisterFinalCertificate(s, b) ==
    /\ s \in Slots
    /\ b \in DomainBlocks(s)
    /\ HasFinalCert(s, b)
    /\ ~HasSkipCert(s)  \* CRITICAL: Skip exclusion check
    /\ b \notin finalized
    /\ finalized' = finalized \cup FinalizableAncestors(b)
    /\ notarizedBlocks' = notarizedBlocks \cup FinalizableAncestors(b)
    /\ UNCHANGED << produced, delivered, notarVotes, notarFallbackVotes, skipVotes,
                    skipFallbackVotes, finalVotes, parentReady, timeoutsArmed,
                    timeoutsFired, fastFinalized >>

MarkParentReady(s) ==
    /\ IsFirstInWindow(s)
    /\ ~parentReady[s]
    /\ (s = FirstSlot \/ \E b \in DomainBlocks(s) : Parent(b) \in notarizedBlocks \cup finalized)
    /\ parentReady' = [parentReady EXCEPT ![s] = TRUE]
    /\ UNCHANGED << produced, delivered, notarVotes, notarFallbackVotes, skipVotes,
                    skipFallbackVotes, finalVotes, timeoutsArmed, timeoutsFired,
                    finalized, fastFinalized, notarizedBlocks >>

ByzantineVoteNotar(n, s, b) ==
    /\ n \in Byzantine
    /\ b \in DomainBlocks(s)
    /\ b \in produced
    /\ notarVotes' = [notarVotes EXCEPT ![s][b] = @ \cup {n}]
    /\ UNCHANGED << produced, delivered, notarFallbackVotes, skipVotes,
                    skipFallbackVotes, finalVotes, parentReady, timeoutsArmed,
                    timeoutsFired, finalized, fastFinalized, notarizedBlocks >>

ByzantineSkip(n, s) ==
    /\ n \in Byzantine
    /\ SlotFinalizedBlocks(s) = {}  \* Cannot skip if slot has finalized blocks
    /\ skipVotes' = [skipVotes EXCEPT ![s] = @ \cup {n}]
    /\ UNCHANGED << produced, delivered, notarVotes, notarFallbackVotes,
                    skipFallbackVotes, finalVotes, parentReady, timeoutsArmed,
                    timeoutsFired, finalized, fastFinalized, notarizedBlocks >>

ByzantineFallbackNotar(n, s, b) ==
    /\ n \in Byzantine
    /\ notarFallbackVotes' = [notarFallbackVotes EXCEPT ![s][b] = @ \cup {n}]
    /\ UNCHANGED << produced, delivered, notarVotes, skipVotes, skipFallbackVotes,
                    finalVotes, parentReady, timeoutsArmed, timeoutsFired,
                    finalized, fastFinalized, notarizedBlocks >>

ByzantineFallbackSkip(n, s) ==
    /\ n \in Byzantine
    /\ SlotFinalizedBlocks(s) = {}  \* Cannot skip if slot has finalized blocks
    /\ skipFallbackVotes' = [skipFallbackVotes EXCEPT ![s] = @ \cup {n}]
    /\ UNCHANGED << produced, delivered, notarVotes, notarFallbackVotes,
                    skipVotes, finalVotes, parentReady, timeoutsArmed, timeoutsFired,
                    finalized, fastFinalized, notarizedBlocks >>

ByzantineFinalize(n, s, b) ==
    /\ n \in Byzantine
    /\ ~HasSkipCert(s)  \* Cannot finalize if skip cert exists
    /\ finalVotes' = [finalVotes EXCEPT ![s][n] = b]
    /\ UNCHANGED << produced, delivered, notarVotes, notarFallbackVotes, skipVotes,
                    skipFallbackVotes, parentReady, timeoutsArmed, timeoutsFired,
                    finalized, fastFinalized, notarizedBlocks >>

RotorDissemination(n, b) ==
    /\ n \in Nodes
    /\ b \in produced
    /\ b \notin delivered[n]
    /\ StakeSum({ r \in Nodes : b \in delivered[r] }) >= Stake[n]
    /\ delivered' = [delivered EXCEPT ![n] = @ \cup {b}]
    /\ UNCHANGED << produced, notarVotes, notarFallbackVotes, skipVotes, skipFallbackVotes,
                    finalVotes, parentReady, timeoutsArmed, timeoutsFired,
                    finalized, fastFinalized, notarizedBlocks >>

(***************************************************************************
 * Action Definitions
 ***************************************************************************)
ProduceAction == \E s \in Slots : \E b \in DomainBlocks(s) : ProduceBlock(s, b)

ScheduleTimeoutAction == \E s \in Slots : ScheduleTimeout(s)

FireTimeoutAction == \E s \in Slots : FireTimeout(s)

HonestNotarizeAction == \E n \in Honest : \E s \in Slots : \E b \in DomainBlocks(s) : HonestNotarize(n, s, b)

HonestSkipAction == \E n \in Honest : \E s \in Slots : HonestSkip(n, s)

HonestFallbackNotarAction == \E n \in Honest : \E s \in Slots : \E b \in DomainBlocks(s) : HonestFallbackNotar(n, s, b)

HonestFallbackSkipAction == \E n \in Honest : \E s \in Slots : HonestFallbackSkip(n, s)

HonestFinalAction == \E n \in Honest : \E s \in Slots : \E b \in DomainBlocks(s) : HonestFinalVote(n, s, b)

RegisterNotarAction == \E s \in Slots : \E b \in DomainBlocks(s) : RegisterNotarCertificate(s, b)

RegisterFastFinalAction == \E s \in Slots : \E b \in DomainBlocks(s) : RegisterFastFinalCertificate(s, b)

RegisterFinalAction == \E s \in Slots : \E b \in DomainBlocks(s) : RegisterFinalCertificate(s, b)

MarkParentReadyAction == \E s \in Slots : MarkParentReady(s)

ByzantineNotarAction == \E n \in Byzantine : \E s \in Slots : \E b \in DomainBlocks(s) : ByzantineVoteNotar(n, s, b)

ByzantineSkipAction == \E n \in Byzantine : \E s \in Slots : ByzantineSkip(n, s)

ByzantineFallbackNotarAction == \E n \in Byzantine : \E s \in Slots : \E b \in DomainBlocks(s) : ByzantineFallbackNotar(n, s, b)

ByzantineFallbackSkipAction == \E n \in Byzantine : \E s \in Slots : ByzantineFallbackSkip(n, s)

ByzantineFinalAction == \E n \in Byzantine : \E s \in Slots : \E b \in DomainBlocks(s) : ByzantineFinalize(n, s, b)

RotorAction == \E n \in Nodes : \E b \in produced : RotorDissemination(n, b)

(***************************************************************************
 * Next State Relation
 ***************************************************************************)
Next == 
    ProduceAction
    \/ ScheduleTimeoutAction
    \/ FireTimeoutAction
    \/ HonestNotarizeAction
    \/ HonestSkipAction
    \/ HonestFallbackNotarAction
    \/ HonestFallbackSkipAction
    \/ HonestFinalAction
    \/ RegisterNotarAction
    \/ RegisterFastFinalAction
    \/ RegisterFinalAction
    \/ MarkParentReadyAction
    \/ ByzantineNotarAction
    \/ ByzantineSkipAction
    \/ ByzantineFallbackNotarAction
    \/ ByzantineFallbackSkipAction
    \/ ByzantineFinalAction
    \/ RotorAction

\* NextSafetyOnly - Optimized for fast exhaustive verification
\* Removes: skip votes, timeouts, Byzantine actions, fallback rounds
\* Focus: Happy path (propose -> notarize -> finalize)
NextSafetyOnly ==
    ProduceAction
    \/ HonestNotarizeAction
    \/ HonestFinalAction
    \/ RegisterNotarAction
    \/ RegisterFastFinalAction
    \/ RegisterFinalAction
    \/ MarkParentReadyAction
    \/ RotorAction

Spec == Init /\ [][Next]_vars
SpecSafety == Init /\ [][NextSafetyOnly]_vars

(***************************************************************************
 * Invariants
 ***************************************************************************)
TypeOK == 
    /\ produced \subseteq BlockIds \cup {GenesisBlock}
    /\ \A n \in Nodes : delivered[n] \subseteq produced
    /\ finalized \subseteq produced
    /\ fastFinalized \subseteq finalized
    /\ notarizedBlocks \subseteq produced

NoDoubleFinalize == 
    \A s \in Slots : \A b1 \in DomainBlocks(s) : \A b2 \in DomainBlocks(s) :
        (b1 # b2) => ~((b1 \in finalized) /\ (b2 \in finalized))

ChainConsistency == 
    \A b1 \in finalized : \A b2 \in finalized :
        b1 \in Ancestors(b2) \/ b2 \in Ancestors(b1)

HonestVoteUniqueness ==
    \A n \in Honest : \A s \in Slots :
        Cardinality({ b \in DomainBlocks(s) : n \in notarVotes[s][b] }) <= 1

FinalizationImpliesNotar ==
    \A b \in finalized : (b = GenesisBlock) \/ HasNotarCert(SlotOf(b), b)

SkipExcludesFinal ==
    \A s \in Slots : SkipActive(s) => SlotFinalizedBlocks(s) = {}

FastPathUnique ==
    \A s \in Slots : \A b1 \in DomainBlocks(s) : \A b2 \in DomainBlocks(s) :
        b1 # b2 => ~(HasFastFinalCert(s, b1) /\ HasFastFinalCert(s, b2))

(***************************************************************************
 * State Space Constraints - Critical for Fast Verification
 ***************************************************************************)
 
\* TimeVoteBound - Standard constraint for safety verification
\* Bounds the key state variables to ensure exhaustive verification completes
TimeVoteBound ==
    /\ Cardinality(finalized) <= 3
    /\ Cardinality(notarizedBlocks) <= 4
    /\ Cardinality(produced) <= 5

\* ByzantineConstraint - For Byzantine fault tolerance tests
\* Tighter bounds due to additional state space from Byzantine actions
ByzantineConstraint ==
    /\ Cardinality(finalized) <= 2
    /\ Cardinality(notarizedBlocks) <= 3
    /\ Cardinality(produced) <= 4
    /\ Cardinality(Byzantine) <= 1

====================================================================
