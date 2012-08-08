module Search where
import Data.Bits
import Data.List(intercalate)
import qualified Data.IntSet as IntSet
import Data.IntSet(IntSet)
import Control.Monad

main = sequence [print i >> print (searchNoCirc i empty (rule a c)) | i <- [1..]]
{-
  Do an exhaustive shallow proof search to see if
  A=>C can be derive from the axiom (A => B if A => B).
  Configuration space is just these axioms,
 -}

data Cfg = A | B | C
  deriving (Show,Eq)

newtype Formula = Formula Int
  deriving Eq
instance Show Formula where
  show (Formula 0) = "False"
  show f = intercalate " \\/ " (map show (filter (flip trueFor f) [A,B,C]))
trueFor :: Cfg -> Formula -> Bool
trueFor A (Formula f) = testBit f 0
trueFor B (Formula f) = testBit f 1
trueFor C (Formula f) = testBit f 2
disj :: Formula -> Formula -> Formula
disj (Formula f1) (Formula f2) = Formula (f1 .|. f2)
conj :: Formula -> Formula -> Formula
conj (Formula f1) (Formula f2) = Formula (f1 .&. f2)
implies :: Formula -> Formula -> Bool
implies (Formula f1) (Formula f2) = 0 == (f1 .&. complement f2)

formulas = map Formula [0..7]

ffalse :: Formula
ffalse = Formula 0
a :: Formula
a = Formula 0x1
b :: Formula
b = Formula 0x2
c :: Formula
c = Formula 0x4

test f c = all (\v -> trueFor v f == (v == c)) [A,B,C]
test1 = test a A && test b B && test c C
test2 = and [implies f1 f2 == implies' f1 f2 | f1 <- formulas, f2 <- formulas]
  where implies' f1 f2 = all (\v -> not (trueFor v f1) || trueFor v f2) [A,B,C]

newtype Rule = Rule Int
  deriving Eq
rule :: Formula -> Formula -> Rule
rule (Formula pre) (Formula post) = Rule (pre `shiftL` 3 .|. post)
pre (Rule r) = Formula (r `shiftR` 3)
post (Rule r) = Formula (r .&. 0x7)

ab = rule a b

instance Show Rule where
  show r = show (pre r)++" => "++show (post r)

newtype RuleSet = RuleSet IntSet
member :: Rule -> RuleSet -> Bool
member (Rule r) (RuleSet s) = IntSet.member r s
insert :: Rule -> RuleSet -> RuleSet
insert (Rule r) (RuleSet s) = RuleSet (IntSet.insert r s)
union :: RuleSet -> RuleSet -> RuleSet
union (RuleSet s1) (RuleSet s2) = RuleSet (IntSet.union s1 s2)
singleton :: Rule -> RuleSet
singleton (Rule r) = RuleSet (IntSet.singleton r)
empty :: RuleSet
empty = RuleSet (IntSet.empty)

searchNoCirc :: Int -> RuleSet -> Rule -> Bool
searchNoCirc depth ready goal | depth < 0 = False
searchNoCirc depth ready goal =
  -- skip (a=>b) rule because we have no circularities to release
  member goal ready -- use a derived rule we added to the axiom set.
  || (pre goal == post goal)  -- reflexivity
  || or [searchNoCirc (depth-1) ready (rule (pre goal) mid)
        && searchNoCirc (depth-1) ready (rule mid (post goal))
        | mid <- formulas] -- transitivity
  || or [searchNoCirc (depth-1) ready (rule f1 f2)
        | f1 <- formulas,
          implies (pre goal) f1,
          f2 <- formulas,
          implies f2 (post goal)] -- consequence
  || or [searchNoCirc (depth-1) ready (rule f1 (post goal))
         && searchNoCirc (depth-1) ready (rule f2 (post goal))
        | f1 <- formulas, f2 <- formulas,
          pre goal == disj f1 f2] -- case
  || search (depth-1) ready (singleton goal) goal -- circularity

search :: Int -> RuleSet -> RuleSet -> Rule -> Bool
search depth ready circ goal | depth < 0 = False
search depth ready circ goal =
  -- use the language rule
  (goal == ab && searchNoCirc (depth-1) (union ready circ) ab)
  || member goal ready -- use a derived rule we added to the axiom set.
     -- reflexivity not allowed
  || or [search (depth-1) ready circ (rule (pre goal) mid)
        && searchNoCirc (depth-1) (union ready circ) (rule mid (post goal))
        | mid <- formulas] -- transitivity
  || or [search (depth-1) ready circ (rule f1 f2)
        | f1 <- formulas,
          implies (pre goal) f1,
          f2 <- formulas,
          implies f2 (post goal)] -- consequence
  || or [search (depth-1) ready circ (rule f1 (post goal))
         && search (depth-1) ready circ (rule f2 (post goal))
        | f1 <- formulas, f2 <- formulas,
          pre goal == disj f1 f2] -- case
  || search (depth-1) ready (insert goal circ) goal -- circularity

data Proof =
  LangRule Proof | Axiom Rule | Refl Formula | Trans Formula Proof Proof | Conseq Proof
  | Case Proof Proof | Circ Proof
  deriving Show

psearchNoCirc :: Int -> RuleSet -> Rule -> Maybe Proof
psearchNoCirc depth ready goal | depth < 0 = Nothing
psearchNoCirc depth ready goal =
  -- skip (a=>b) rule because we have no circularities to release
  (guard (member goal ready) >> return (Axiom goal))
      -- use a derived rule we added to the axiom set.
  `mplus`
  (guard (pre goal == post goal) >> return (Refl (pre goal))) -- reflexivity
  `mplus` msum
      [liftM2 (Trans mid)
        (psearchNoCirc (depth-1) ready (rule (pre goal) mid))
        (psearchNoCirc (depth-1) ready (rule mid (post goal)))
        | mid <- formulas] -- transitivity
  `mplus` msum
       [liftM Conseq (psearchNoCirc (depth-1) ready (rule f1 f2))
        | f1 <- formulas,
          implies (pre goal) f1,
          f2 <- formulas,
          implies f2 (post goal)] -- consequence
  `mplus` msum
        [liftM2 Case (psearchNoCirc (depth-1) ready (rule f1 (post goal)))
                     (psearchNoCirc (depth-1) ready (rule f2 (post goal)))
        | f1 <- formulas, f2 <- formulas,
          pre goal == disj f1 f2] -- case
  `mplus` liftM Circ (psearch (depth-1) ready (singleton goal) goal) -- circularity

psearch :: Int -> RuleSet -> RuleSet -> Rule -> Maybe Proof
psearch depth ready circ goal | depth < 0 = Nothing
psearch depth ready circ goal =
  -- use the language rule
  (guard (goal == ab) >>
     liftM LangRule (psearchNoCirc (depth-1) (union ready circ) ab))
  `mplus`
  (guard (member goal ready) >> return (Axiom goal))
      -- use a derived rule we added to the axiom set.
     -- reflexivity not allowed
  `mplus` msum
      [liftM2 (Trans mid)
        (psearch (depth-1) ready circ (rule (pre goal) mid))
        (psearchNoCirc (depth-1) (union ready circ) (rule mid (post goal)))
        | mid <- formulas] -- transitivity
  `mplus` msum
       [liftM Conseq (psearch (depth-1) ready circ (rule f1 f2))
        | f1 <- formulas,
          implies (pre goal) f1,
          f2 <- formulas,
          implies f2 (post goal)] -- consequence
  `mplus` msum
        [liftM2 Case (psearch (depth-1) ready circ (rule f1 (post goal)))
                     (psearch (depth-1) ready circ (rule f2 (post goal)))
        | f1 <- formulas, f2 <- formulas,
          pre goal == disj f1 f2] -- case
  `mplus` liftM Circ (psearch (depth-1) ready (insert goal circ) goal) -- circularity

examples :: [Maybe Proof]
examples = [
  psearchNoCirc 2 empty (rule a b),
  psearchNoCirc 2 (singleton (rule a a)) (rule a a),
  psearch 1 (singleton (rule a b)) (singleton (rule b c)) (rule a c),
  psearchNoCirc 2 (singleton (rule a a)) (rule a c),
  psearchNoCirc 1 (singleton (rule (disj a b) c)) (rule a c)
  ]
  