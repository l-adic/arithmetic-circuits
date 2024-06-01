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

truncateLabel :: Text -> Text
truncateLabel l
  | Text.length l > 1000 = Text.take 1000 l <> "..."
  | otherwise = l

data Node = Node
  { nLabel :: Text,
    nId :: Text
  }

renderNode :: Node -> Text
renderNode Node {..} = nId <> " [label=\"" <> truncateLabel nLabel <> "\"]"

data PointNode = PointNode Text

renderPointNode :: PointNode -> Text
renderPointNode (PointNode _id) = _id <> " [shape=point]"

data Color
  = Black
  | Red

renderColor :: Color -> Text
renderColor Black = "black"
renderColor Red = "red"

data Arrow = Arrow
  { aSourceId :: Text,
    aLabel :: Maybe Text,
    aColor :: Color,
    aTargetId :: Text
  }

renderArrow :: Arrow -> Text
renderArrow Arrow {..} =
  let atters =
        catMaybes
          [ fmap (\l -> "label=\"" <> truncateLabel l <> "\"") aLabel,
            Just $ "color=\"" <> renderColor aColor <> "\""
          ]
   in aSourceId <> " -> " <> aTargetId <> " [" <> Text.intercalate ", " atters <> "]"

data DotItem
  = DINode Node
  | DIPNode PointNode
  | DIArrow Arrow

renderDotItem :: DotItem -> Text
renderDotItem = \case
  DINode n -> renderNode n
  DIPNode n -> renderPointNode n
  DIArrow a -> renderArrow a

arithCircuitToDot ::
  (Pretty f) =>
  ArithCircuit f ->
  Text
arithCircuitToDot c@(ArithCircuit gates) =
  Text.unlines
    . wrapInDigraph
    . concatMap (map renderDotItem . gateToDotItems)
    $ gates
  where
    bWs = booleanWires c
    color w = if w `elem` bWs then Red else Black
    wrapInDigraph x = ["digraph g {"] ++ x ++ ["}"]
    dotWire :: Wire -> Text
    dotWire = show . pretty

    gateToDotItems ::
      (Pretty f) =>
      Gate f Wire ->
      [DotItem]
    gateToDotItems (Mul lhs rhs output) =
      let gateId = dotWire output
          out =
            Node
              { nLabel = "*",
                nId = gateId
              }
          l =
            Node
              { nLabel = show $ pretty lhs,
                nId = gateId <> "lhs"
              }
          lArr =
            Arrow
              { aSourceId = nId l,
                aLabel = Nothing,
                aColor = Black,
                aTargetId = nId out
              }
          r =
            Node
              { nLabel = show $ pretty rhs,
                nId = gateId <> "rhs"
              }
          rArr =
            Arrow
              { aSourceId = nId r,
                aLabel = Nothing,
                aColor = Black,
                aTargetId = nId out
              }
       in [DINode out, DINode l, DINode r, DIArrow lArr, DIArrow rArr]
            <> maybeOutputs output
            <> map (DIArrow . mkInputArrow (nId l)) (toList lhs)
            <> map (DIArrow . mkInputArrow (nId r)) (toList rhs)
      where
        mkInputArrow :: Text -> Wire -> Arrow
        mkInputArrow inputId srcWire =
          Arrow
            { aSourceId = dotWire srcWire,
              aLabel = Just $ show (pretty srcWire),
              aColor = color srcWire,
              aTargetId = inputId
            }
    gateToDotItems (Equal i m output) =
      let gateId = dotWire output
          -- output node
          out =
            Node
              { nLabel = "= 0 ? 0 : 1",
                nId = gateId
              }
          lArr =
            Arrow
              { aSourceId = dotWire i,
                aLabel = Just $ dotWire i,
                aColor = color i,
                aTargetId = nId out
              }
          rArr =
            Arrow
              { aSourceId = dotWire m,
                aLabel = Just $ dotWire m,
                aColor = color m,
                aTargetId = nId out
              }
       in [DINode out, DIArrow lArr, DIArrow rArr] <> maybeOutputs output
    gateToDotItems (Split i outputs) =
      let gateId = Text.concat . fmap dotWire $ outputs
          out =
            Node
              { nLabel = "split",
                nId = gateId
              }
          outArr =
            Arrow
              { aSourceId = dotWire i,
                aLabel = Just $ dotWire i,
                aColor = color i,
                aTargetId = gateId
              }
          mkSplitWire output =
            Arrow
              { aSourceId = nId out,
                aLabel = Nothing,
                aColor = color output,
                aTargetId = dotWire output
              }
       in [DINode out, DIArrow outArr]
            <> concatMap maybeOutputs outputs
            <> map (DIPNode . PointNode . dotWire) outputs
            <> map (DIArrow . mkSplitWire) outputs
    gateToDotItems (Boolean _) = []

    maybeOutputs :: Wire -> [DotItem]
    maybeOutputs w@(OutputWire i) =
      let gateId = "out_" <> show i
          out = PointNode gateId
          outArr =
            Arrow
              { aSourceId = dotWire w,
                aLabel = Just $ show (pretty w),
                aColor = color w,
                aTargetId = gateId
              }
       in [DIPNode out, DIArrow outArr]
    maybeOutputs _ = []
