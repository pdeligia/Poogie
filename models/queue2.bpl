type Event = int;

const unique $NULL: int;
axiom $NULL == 0;

const unique _ping: Event;
const unique _pong: Event;

var $Inbox: [int]Queue;

type {:datatype} Queue;

function {:constructor} $queue() : Queue;
function {:constructor} $q_cons(e:Event, q:Queue) : Queue;

function $q_first(Queue) returns (Event);
function $q_tail(Queue) returns (Queue);
function $q_length(Queue) returns (int);
function $q_index(int, Queue) returns (Event);
function $q_remove(int, Queue) returns (Queue);
function $q_enqueue(Event, Queue) returns (Queue);

axiom $q_length($queue()) == 0;
axiom (forall e:Event, q:Queue :: $q_length($q_cons(e, q)) == 1 + $q_length(q));

axiom (forall e:Event, q:Queue :: $q_first($queue()) == $NULL);
axiom (forall e:Event, q:Queue :: $q_first($q_cons(e, q)) == e);

axiom (forall e:Event, q:Queue :: $q_tail($queue()) == $queue());
axiom (forall e:Event, q:Queue :: $q_tail($q_cons(e, q)) == q);

axiom (forall i:int, q:Queue :: {$q_index(i, q)} $q_index(i, q) ==
  if i == 0 then $q_first(q)
  else $q_index(i - 1, $q_tail(q)));

axiom (forall i:int, q:Queue :: {$q_remove(i, q)} $q_remove(i, q) ==
  if i == 0 then $q_tail(q)
  else $q_cons($q_first(q), $q_remove(i - 1, $q_tail(q))));

axiom (forall e:Event, q:Queue :: {$q_enqueue(e, q)} $q_enqueue(e, q) ==
  if q == $queue() then $q_cons(e, q)
  else $q_cons($q_first(q), $q_enqueue(e, $q_tail(q))));


// Test harness
procedure {:entrypoint} Main();
  modifies $Inbox;

implementation {:entrypoint} Main()
{
  $main:
    $Inbox[0] := $queue();
    assert $q_length($Inbox[0]) == 0;
    assert $q_first($Inbox[0]) == $NULL;

    $Inbox[0] := $q_cons(_ping, $Inbox[0]);
    assert $q_length($Inbox[0]) == 1;
    assert $q_length($q_tail($Inbox[0])) == 0;
    assert $q_first($Inbox[0]) == _ping;

    $Inbox[0] := $q_cons(_pong, $Inbox[0]);
    assert $q_length($Inbox[0]) == 2;
    assert $q_first($Inbox[0]) == _pong;

    assert $q_index(0, $Inbox[0]) == _pong;
    assert $q_index(1, $Inbox[0]) == _ping;

    $Inbox[0] := $q_remove(0, $Inbox[0]);
    assert $q_index(0, $Inbox[0]) == _ping;

    $Inbox[0] := $queue();
    $Inbox[0] := $q_enqueue(_ping, $Inbox[0]);
    assert $q_length($Inbox[0]) == 1;
    assert $q_first($Inbox[0]) == _ping;

    $Inbox[0] := $q_enqueue(_pong, $Inbox[0]);
    $Inbox[0] := $q_enqueue(_pong, $Inbox[0]);
    assert $q_length($Inbox[0]) == 3;
    assert $q_first($Inbox[0]) == _ping;

    $Inbox[0] := $q_remove(0, $Inbox[0]);
    assert $q_index(0, $Inbox[0]) == _pong;

    return;
}
