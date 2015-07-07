type Event = int;
const unique $NULL: int;
axiom $NULL == 0;

const unique _ping: Event;
const unique _pong: Event;

var $Inbox: [int]Queue Event;

type Queue Event;

function $q_empty() returns (Queue Event);
function $q_cons(Event, Queue Event) returns (Queue Event);
function $q_first(Queue Event) returns (Event);
function $q_tail(Queue Event) returns (Queue Event);
function $q_length(Queue Event) returns (int);
function $q_index(int, Queue Event) returns (Event);
function $q_remove(int, Queue Event) returns (Queue Event);
function $q_enqueue(Event, Queue Event) returns (Queue Event);

axiom $q_length($q_empty()) == 0;
axiom (forall e:Event, q:Queue Event :: $q_length($q_cons(e, q)) == 1 + $q_length(q));

axiom (forall e:Event, q:Queue Event :: $q_first($q_empty()) == $NULL);
axiom (forall e:Event, q:Queue Event :: $q_first($q_cons(e, q)) == e);

axiom (forall e:Event, q:Queue Event :: $q_tail($q_empty()) == $q_empty());
axiom (forall e:Event, q:Queue Event :: $q_tail($q_cons(e, q)) == q);

axiom (forall i:int, q:Queue Event :: {$q_index(i, q)} $q_index(i, q) ==
  if i == 0 then $q_first(q)
  else $q_index(i - 1, $q_tail(q)));

axiom (forall i:int, q:Queue Event :: {$q_remove(i, q)} $q_remove(i, q) ==
  if i == 0 then $q_tail(q)
  else $q_cons($q_first(q), $q_remove(i - 1, $q_tail(q))));

axiom (forall e:Event, q:Queue Event :: {$q_enqueue(e, q)} $q_enqueue(e, q) ==
  if q == $q_empty() then $q_cons(e, q)
  else $q_cons($q_first(q), $q_enqueue(e, $q_tail(q))));


// Test harness
procedure {:entrypoint} Main();
  modifies $Inbox;

implementation {:entrypoint} Main()
{
  $main:
    $Inbox[0] := $q_empty();
    assert $q_length($Inbox[0]) == 0;
    assert $q_first($Inbox[0]) == $NULL;

    $Inbox[0] := $q_cons(_ping, $Inbox[0]);
    assert $q_length($Inbox[0]) == 1;
    assert $q_first($Inbox[0]) == _ping;

    $Inbox[0] := $q_cons(_pong, $Inbox[0]);
    assert $q_length($Inbox[0]) == 2;
    assert $q_first($Inbox[0]) == _pong;

    assert $q_index(0, $Inbox[0]) == _pong;
    assert $q_index(1, $Inbox[0]) == _ping;

    $Inbox[0] := $q_remove(0, $Inbox[0]);
    assert $q_index(0, $Inbox[0]) == _ping;

    $Inbox[0] := $q_empty();
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
