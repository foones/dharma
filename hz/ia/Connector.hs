module Connector(
	ConnectorM, runConnectorM, Message, messagePipe,
	connGet, connPut, connModify
) where

import System.IO
import Control.Monad

---

data ConnectorM state a = CM (state -> IO (state, a))

instance Monad (ConnectorM state) where
  return x   = CM (\ s0 -> return (s0, x))
  CM f >>= g = CM (\ s0 -> do
                   (s1, x) <- f s0
                   case g x of
                       CM g' -> g' s1)

mLiftIO :: IO a -> ConnectorM state a
mLiftIO f = CM (\ s0 -> do
                x <- f
                return (s0, x))

runConnectorM :: state -> ConnectorM state a -> IO a
runConnectorM s0 (CM f) = do
  (s1, x) <- f s0
  return x

---

connGet :: ConnectorM state state
connGet = CM (\ s -> return (s, s))

connModify :: (state -> state) -> ConnectorM state ()
connModify f = CM (\ s -> return (f s, ()))

connPut :: state -> ConnectorM state ()
connPut = connModify . const

---

type Message = String

connGetMessage :: ConnectorM state Message
connGetMessage = mLiftIO getLine

connPutMessage :: Message -> ConnectorM state ()
connPutMessage x = mLiftIO $ do
                 putStr (x ++ "\n")
                 hFlush stdout

---

messagePipe :: (Message -> ConnectorM state Message) -> ConnectorM state ()
messagePipe f = do
  input <- connGetMessage
  if input == "END"
    then return ()
    else do
        output <- f input
        connPutMessage output
        messagePipe f

