module Main where 

import Connector
import IA

--- Main

type GameState = Int
type GameM = ConnectorM GameState

nextState :: Message -> GameM Message
nextState "hola" = return "chau"
nextState _      = return "otra_cosa"
{-
nextState _      = do
  s <- connGet
  connModify (+1)
  return ("otra cosa" ++ show s)
-}

--- Main

connect :: GameState -> IO ()
connect s0 = runConnectorM s0 $ messagePipe nextState

main :: IO ()
main = connect 0

