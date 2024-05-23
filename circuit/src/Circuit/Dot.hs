-- | Visualise circuits using Graphviz
module Circuit.Dot
  ( arithCircuitToDot,
  )
where

import Circuit.Affine ()
import Circuit.Arithmetic (ArithCircuit (..), Gate (..), Wire (..), booleanWires)
import Data.Text qualified as Text
import Protolude
import Text.PrettyPrint.Leijen.Text (Pretty (..))

arithCircuitToDot ::
  (Pretty f) => ArithCircuit f -> Text
arithCircuitToDot c@(ArithCircuit gates) =
  Text.unlines . wrapInDigraph . concatMap graphGate $ gates
  where
    bWs = booleanWires c
    color w = if w `elem` bWs then "red" else "black"
    wrapInDigraph x = ["digraph g {"] ++ x ++ ["}"]

    dotWire :: Wire -> Text
    dotWire = show . pretty

    dotArrow :: Text -> Text -> Text
    dotArrow s t = s <> " -> " <> t

    dotArrowLabel :: Text -> Text -> Text -> Text -> Text
    dotArrowLabel s t lbl _c =
      dotArrow s t <> " [label=\"" <> (truncateLabel lbl) <> "\", color=\"" <> _c <> "\"]"

    labelNode lblId lbl = lblId <> " [label=\"" <> truncateLabel lbl <> "\"]"

    pointNode lblId = lblId <> " [shape=point]"

    truncateLabel :: Text -> Text
    truncateLabel l
      | Text.length l > 1000 = Text.take 1000 l <> "..."
      | otherwise = l

    graphGate :: (Pretty f) => Gate f Wire -> [Text]
    graphGate (Mul lhs rhs output) =
      [ labelNode gateLabel "*",
        labelNode lhsLabel (show $ pretty lhs),
        dotArrow lhsLabel gateLabel,
        labelNode rhsLabel (show $ pretty rhs),
        dotArrow rhsLabel gateLabel
      ]
        ++ inputs lhs lhsLabel
        ++ inputs rhs rhsLabel
      where
        lhsLabel = dotWire output <> "lhs"
        rhsLabel = dotWire output <> "rhs"
        gateLabel = dotWire output
        inputs circuit tgt =
          map
            ( \a ->
                (\src -> dotArrowLabel src tgt (show $ pretty src) (color a))
                  . dotWire
                  $ a
            )
            $ toList circuit
    graphGate (Equal i m output) =
      [ labelNode gateLabel "= 0 ? 0 : 1",
        dotArrowLabel (dotWire i) gateLabel (dotWire i) (color i),
        dotArrowLabel (dotWire m) gateLabel (dotWire m) (color m)
      ]
      where
        gateLabel = dotWire output
    graphGate (Split i outputs) =
      [ labelNode gateLabel "split",
        dotArrowLabel (dotWire i) gateLabel (dotWire i) (color i)
      ]
        ++ map (pointNode . dotWire) outputs
        ++ map (\output -> dotArrow gateLabel (dotWire output)) outputs
      where
        gateLabel = Text.concat . fmap dotWire $ outputs
    graphGate (Boolean _) = []
