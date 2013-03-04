module IA where 

import Connector

type GameState = Int

type GameM = ConnectorM GameState

connect :: GameState -> IO ()
connect s0 = runConnectorM s0 $ messagePipe nextState

nextState :: Message -> GameM Message
nextState "hola" = return "chau"
nextState _      = do
  s <- connGet
  connModify (+1)
  return ("otra cosa" ++ show s)

main :: IO ()
main = connect 0

