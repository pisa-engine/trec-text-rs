var searchIndex={};
searchIndex["anyhow"] = {"doc":"This library provides [`anyhow::Error`][Error], a trait…","i":[[3,"Error","anyhow","The `Error` type, a wrapper around a dynamic error type.",null,null],[3,"Chain","","Iterator of a chain of source errors.",null,null],[11,"new","","",0,[[["stderror"]],["self"]]],[11,"new","","Create a new error object from any error type.",1,[[["e"]],["self"]]],[11,"msg","","Create a new error object from a printable error message.",1,[[["m"]],["self"]]],[11,"context","","Wrap the error value with additional context.",1,[[["c"]],["self"]]],[11,"backtrace","","Get the backtrace for this Error.",1,[[["self"]],["backtrace"]]],[11,"chain","","An iterator of the chain of source errors contained by…",1,[[["self"]],["chain"]]],[11,"root_cause","","The lowest level cause of this error — this error's…",1,[[["self"]],["stderror"]]],[11,"is","","Returns true if `E` is the type held by this error object.",1,[[["self"]],["bool"]]],[11,"downcast","","Attempt to downcast the error object to a concrete type.",1,[[],["result"]]],[11,"downcast_ref","","Downcast this error object by reference.",1,[[["self"]],[["option"],["e"]]]],[11,"downcast_mut","","Downcast this error object by mutable reference.",1,[[["self"]],[["option"],["e"]]]],[6,"Result","","`Result<T, Error>`",null,null],[8,"Context","","Provides the `context` method for `Result`.",null,null],[10,"context","","Wrap the error value with additional context.",2,[[["c"]],[["result",["error"]],["error"]]]],[10,"with_context","","Wrap the error value with additional context that is…",2,[[["f"]],[["result",["error"]],["error"]]]],[14,"bail","","Return early with an error.",null,null],[14,"ensure","","Return early with an error if a condition is not satisfied.",null,null],[14,"anyhow","","Construct an ad-hoc error from a string.",null,null],[11,"from","","",1,[[],["t"]]],[11,"from","","",1,[[["t"]],["t"]]],[11,"into","","",1,[[],["u"]]],[11,"to_string","","",1,[[["self"]],["string"]]],[11,"try_from","","",1,[[["u"]],["result"]]],[11,"try_into","","",1,[[],["result"]]],[11,"borrow","","",1,[[["self"]],["t"]]],[11,"borrow_mut","","",1,[[["self"]],["t"]]],[11,"type_id","","",1,[[["self"]],["typeid"]]],[11,"from","","",0,[[["t"]],["t"]]],[11,"into","","",0,[[],["u"]]],[11,"into_iter","","",0,[[],["i"]]],[11,"to_owned","","",0,[[["self"]],["t"]]],[11,"clone_into","","",0,[[["self"],["t"]]]],[11,"try_from","","",0,[[["u"]],["result"]]],[11,"try_into","","",0,[[],["result"]]],[11,"borrow","","",0,[[["self"]],["t"]]],[11,"borrow_mut","","",0,[[["self"]],["t"]]],[11,"type_id","","",0,[[["self"]],["typeid"]]],[11,"drop","","",1,[[["self"]]]],[11,"as_ref","","",1,[[["self"]],["stderror"]]],[11,"as_ref","","",1,[[["self"]],["stderror"]]],[11,"from","","",1,[[["e"]],["self"]]],[11,"next_back","","",0,[[["self"]],["option"]]],[11,"len","","",0,[[["self"]],["usize"]]],[11,"next","","",0,[[["self"]],["option"]]],[11,"size_hint","","",0,[[["self"]]]],[11,"clone","","",0,[[["self"]],["chain"]]],[11,"default","","",0,[[],["self"]]],[11,"deref","","",1,[[["self"]]]],[11,"deref_mut","","",1,[[["self"]]]],[11,"fmt","","",1,[[["formatter"],["self"]],["result"]]],[11,"fmt","","",1,[[["formatter"],["self"]],["result"]]]],"p":[[3,"Chain"],[3,"Error"],[8,"Context"]]};
searchIndex["trec_text"] = {"doc":"Parsing TREC Text format.","i":[[6,"Result","trec_text","`Result<T, Error>`",null,null],[3,"DocumentRecord","","TREC Text record data.",null,null],[3,"Parser","","TREC Text format parser.",null,null],[11,"docno","","Retrieves `DOCNO` field bytes. Any whitespaces proceeding…",0,[[["self"]]]],[11,"content","","Retrieves content bytes.",0,[[["self"]]]],[11,"new","","Consumes the reader and returns a new TREC Text parser…",1,[[["r"]],["self"]]],[11,"into_bytes","","Returns the underlying iterator of remaining bytes.",1,[[]]],[11,"from","","",0,[[["t"]],["t"]]],[11,"into","","",0,[[],["u"]]],[11,"to_owned","","",0,[[["self"]],["t"]]],[11,"clone_into","","",0,[[["self"],["t"]]]],[11,"try_from","","",0,[[["u"]],["result"]]],[11,"try_into","","",0,[[],["result"]]],[11,"borrow","","",0,[[["self"]],["t"]]],[11,"borrow_mut","","",0,[[["self"]],["t"]]],[11,"type_id","","",0,[[["self"]],["typeid"]]],[11,"from","","",1,[[["t"]],["t"]]],[11,"into","","",1,[[],["u"]]],[11,"into_iter","","",1,[[],["i"]]],[11,"try_from","","",1,[[["u"]],["result"]]],[11,"try_into","","",1,[[],["result"]]],[11,"borrow","","",1,[[["self"]],["t"]]],[11,"borrow_mut","","",1,[[["self"]],["t"]]],[11,"type_id","","",1,[[["self"]],["typeid"]]],[11,"next","","",1,[[["self"]],["option"]]],[11,"clone","","",0,[[["self"]],["documentrecord"]]],[11,"eq","","",0,[[["documentrecord"],["self"]],["bool"]]],[11,"ne","","",0,[[["documentrecord"],["self"]],["bool"]]],[11,"fmt","","",0,[[["formatter"],["self"]],["result"]]]],"p":[[3,"DocumentRecord"],[3,"Parser"]]};
addSearchOptions(searchIndex);initSearch(searchIndex);