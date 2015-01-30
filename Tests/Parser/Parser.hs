import Language.Hakaru.Parser.Parser
import Control.Monad

t1 = "test1.hk"
t2 = "test2.hk"
t3 = "test3.hk"
t4 = "test4.hk"
t5 = "test5.hk"
t6 = "test6.hk"
t7 = "test7.hk"
t8 = "test8.hk"
t9 = "test9.hk"

parseAndTest t = readFile ("Tests/Parser/" ++ t) >>= print . parseHakaru

main = mapM_ parseAndTest [t1,t2,t3,t4,t5,t6,t7,t8,t9]
