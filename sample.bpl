// Program
var $CurrMid: int;
var $MType: [int]Machine;

var $Heap: [int][int]int;
var $State: [int]State;
var $IsHalted: [int]bool;

var $Raised: [int]Event;
var $Inbox: [int]Queue;

var $Payload: [int]Payload;

var $Ignores: [int][Event]bool;
var $Defers: [int][Event]bool;


// Types
type Machine;
type State;
type Event;
type Payload = int;

const unique $DEFAULT: Event;
const unique $HALT: Event;

const unique $NULL: int;
axiom $NULL == 0;


// Event queue

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

axiom (forall e:Event, q:Queue :: $q_first($queue()) == $DEFAULT);
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


// Machinery
procedure {:inline 1} $create_machine(m: Machine, p: Payload) returns (r: int);
  modifies $CurrMid, $MType, $Heap, $State, $IsHalted, $Raised, $Inbox, $Payload;

implementation {:inline 1} $create_machine(m: Machine, p: Payload) returns (mid: int)
{
  $bb0:
    assume $CurrMid > 0;
    mid := $CurrMid;
    $CurrMid := $CurrMid + 1;

    $Payload[mid] := p;

    if (m == _machine.server)
    {
      $MType[mid] := _machine.server;
      call _machine.server.constructor(mid);
    }
    else if (m == _machine.client)
    {
      $MType[mid] := _machine.client;
      call _machine.client.constructor(mid);
    }

    return;
}

procedure {:inline 1} $raise(mid: int, e: Event, p: Payload);
  modifies $Heap, $State, $IsHalted, $Raised, $Inbox, $Payload;

implementation {:inline 1} $raise(mid: int, e: Event, p: Payload)
{
  $bb0:
    $Payload[mid] := p;
    $Raised[mid] := e;
    call $run_event_handler(mid);
    return;
}

procedure {:inline 1} $send(mid: int, e: Event, p: Payload);
  modifies $Inbox, $Payload;

implementation {:inline 1} $send(mid: int, e: Event, p: Payload)
{
  $bb0:
    $Payload[mid] := p;
    $Inbox[mid] := $q_enqueue(e, $Inbox[mid]);
    async call $run_event_handler(mid);
    return;
}

procedure {:inline 1} $run_event_handler(mid: int);
  modifies $Heap, $State, $IsHalted, $Raised, $Inbox, $Payload;

implementation {:inline 1} $run_event_handler(mid: int)
{
  var nextEvent: Event;

  $bb0:
    // yield;
    nextEvent := $DEFAULT;

    if ($IsHalted[mid])
    {
      return;
    }

    // while (!$IsHalted[mid])
    // {
    //   call nextEvent := $get_next_event(mid);
    //
    //   if (nextEvent == $DEFAULT)
    //   {
    //     break;
    //   }
    //
    //   call $handle_event(mid, nextEvent);
    // }

    call nextEvent := $get_next_event(mid);

    if (nextEvent == $DEFAULT)
    {
      return;
    }

    call $handle_event(mid, nextEvent);

    return;
}

procedure {:inline 1} $get_next_event(mid: int) returns (r: Event);
  modifies $Raised, $Inbox;

implementation {:inline 1} $get_next_event(mid: int) returns (r: Event)
{
  var nextEvent: Event;
  var index: int;
  var size: int;

  $bb0:
    nextEvent := $DEFAULT;

    if ($Raised[mid] != $DEFAULT)
    {
      nextEvent := $Raised[mid];
      $Raised[mid] := $DEFAULT;
    }
    else if ($q_length($Inbox[mid]) > 0)
    {
      index := 0;
      while (index < $q_length($Inbox[mid]))
      {
        if ($Ignores[mid][$q_index(index, $Inbox[mid])])
        {
          $Inbox[mid] := $q_remove(index, $Inbox[mid]);
          index := index - 1;
        }
        else if (!$Defers[mid][$q_index(index, $Inbox[mid])])
        {
          nextEvent := $q_index(index, $Inbox[mid]);
          $Inbox[mid] := $q_remove(index, $Inbox[mid]);
          break;
        }

        index := index + 1;
      }
    }

    r := nextEvent;
    return;
}

procedure {:inline 1} $handle_event(mid: int, e: Event);
  modifies $Heap, $State, $IsHalted, $Raised, $Inbox, $Payload;

implementation {:inline 1} $handle_event(mid: int, e: Event)
{
  $bb0:
    if (e == $HALT)
    {
      $IsHalted[mid] := true;
      return;
    }

    if ($MType[mid] == _machine.server)
    {
      call _machine.server.handle_event(mid, e);
    }
    else if ($MType[mid] == _machine.client)
    {
      call _machine.client.handle_event(mid, e);
    }

    return;
}


// Events
const unique _event.ping: Event;
const unique _event.pong: Event;
const unique _event.unit: Event;


// Machine: server
const {:main} unique _machine.server: Machine;
const {:start} unique _machine.server.init: State;
const unique _machine.server.playing: State;

const unique _machine.server.client: int;

procedure {:inline 1} _machine.server.constructor(mid: int);
  modifies $MType, $Heap, $State, $IsHalted, $Raised, $Inbox;

implementation {:inline 1} _machine.server.constructor(mid: int)
{
  $bb0:
    $IsHalted[mid] := false;
    $Inbox[mid] := $queue();
    $State[mid] := _machine.server.init;
    $Raised[mid] := $DEFAULT;
    $Heap[mid][_machine.server.client] := $NULL;
    async call _machine.server.start(mid);
    return;
}

procedure {:inline 1} _machine.server.start(mid: int);
  modifies $CurrMid, $MType, $Heap, $State, $IsHalted, $Raised, $Inbox, $Payload;

implementation {:inline 1} _machine.server.start(mid: int)
{
  $bb0:
    // yield;
    call _machine.server.init.entry(mid);
    return;
}

procedure {:inline 1} _machine.server.handle_event(mid: int, e: Event);
  modifies $State, $Raised, $Inbox, $Payload;

implementation {:inline 1} _machine.server.handle_event(mid: int, e: Event)
{
  $bb0:
    if ($State[mid] == _machine.server.init)
    {
      if (e == _event.unit)
      {
        call _machine.server.goto_state(mid, _machine.server.playing);
      }
    }
    else if ($State[mid] == _machine.server.playing)
    {
      if (e == _event.ping)
      {
        call _machine.server.sendPong(mid);
      }
    }

    return;
}

procedure {:inline 1} _machine.server.goto_state(mid: int, s: State);
  modifies $State, $Inbox, $Payload;

implementation {:inline 1} _machine.server.goto_state(mid: int, s: State)
{
  $bb0:
    $State[mid] := s;
    if (s == _machine.server.playing)
    {
      call _machine.server.playing.entry(mid);
    }

    return;
}

procedure {:inline 1} {:entry} _machine.server.init.entry(mid: int);
  modifies $CurrMid, $MType, $IsHalted, $Heap, $State, $Raised, $Inbox, $Payload;

implementation {:inline 1} {:entry} _machine.server.init.entry(mid: int)
{
  var client: int;

  $bb0:
    call client := $create_machine(_machine.client, mid);
    $Heap[mid][_machine.server.client] := client;
    call $raise(mid, _event.unit, $NULL);
    return;
}

procedure {:inline 1} {:entry} _machine.server.playing.entry(mid: int);
  modifies $Inbox, $Payload;

implementation {:inline 1} {:entry} _machine.server.playing.entry(mid: int)
{
  $bb0:
    call _machine.server.sendPong(mid);
    return;
}

procedure {:inline 1} _machine.server.sendPong(mid: int);
  modifies $Inbox, $Payload;

implementation {:inline 1} _machine.server.sendPong(mid: int)
{
  $bb0:
    call $send($Heap[mid][_machine.server.client], _event.pong, $NULL);
    return;
}


// Machine: client
const unique _machine.client: Machine;
const {:start} unique _machine.client.init: State;
const unique _machine.client.playing: State;

const unique _machine.client.server: int;
const unique _machine.client.counter: int;

procedure {:inline 1} _machine.client.constructor(mid: int);
  modifies $MType, $Heap, $State, $IsHalted, $Raised, $Inbox;

implementation {:inline 1} _machine.client.constructor(mid: int)
{
  $bb0:
    $IsHalted[mid] := false;
    $Inbox[mid] := $queue();
    $State[mid] := _machine.client.init;
    $Raised[mid] := $DEFAULT;
    $Heap[mid][_machine.client.server] := $NULL;
    $Heap[mid][_machine.client.counter] := 0;
    async call _machine.client.start(mid);
    return;
}

procedure {:inline 1} _machine.client.start(mid: int);
  modifies $CurrMid, $MType, $Heap, $State, $IsHalted, $Raised, $Inbox, $Payload;

implementation {:inline 1} _machine.client.start(mid: int)
{
  $bb0:
    // yield;
    call _machine.client.init.entry(mid);
    return;
}

procedure {:inline 1} _machine.client.handle_event(mid: int, e: Event);
  modifies $Heap, $State, $IsHalted, $Raised, $Inbox, $Payload;

implementation {:inline 1} _machine.client.handle_event(mid: int, e: Event)
{
  $bb0:
    if ($State[mid] == _machine.client.init)
    {
      if (e == _event.unit)
      {
        call _machine.client.goto_state(mid, _machine.client.playing);
      }
    }
    else if ($State[mid] == _machine.client.playing)
    {
      if (e == _event.unit)
      {
        call _machine.client.goto_state(mid, _machine.client.playing);
      }
      else if (e == _event.pong)
      {
        call _machine.client.sendPing(mid);
      }
    }

    return;
}

procedure {:inline 1} _machine.client.goto_state(mid: int, s: State);
  modifies $State, $Inbox;

implementation {:inline 1} _machine.client.goto_state(mid: int, s: State)
{
  $bb0:
    $State[mid] := s;
    if (s == _machine.client.playing)
    {
      call _machine.client.playing.entry(mid);
    }

    return;
}

procedure {:inline 1} {:entry} _machine.client.init.entry(mid: int);
  modifies $CurrMid, $MType, $Heap, $State, $IsHalted, $Raised, $Inbox, $Payload;

implementation {:inline 1} {:entry} _machine.client.init.entry(mid: int)
{
  var client: int;

  $bb0:
    $Heap[mid][_machine.client.server] := $Payload[mid];
    call $raise(mid, _event.unit, $NULL);
    return;
}

procedure {:inline 1} {:entry} _machine.client.playing.entry(mid: int);

implementation {:inline 1} {:entry} _machine.client.playing.entry(mid: int)
{
  $bb0:
    if ($Heap[mid][_machine.client.counter] == 1)
    {
      // call $raise(mid, $HALT, $NULL);return;
      assert false;
    }

    return;
}

procedure {:inline 1} _machine.client.sendPing(mid: int);
  modifies $Heap, $State, $IsHalted, $Raised, $Inbox, $Payload;

implementation {:inline 1} _machine.client.sendPing(mid: int)
{
  $bb0:
    // assert false;
    $Heap[mid][_machine.client.counter] := $Heap[mid][_machine.client.counter] + 1;
    call $send($Heap[mid][_machine.client.server], _event.ping, $NULL);
    call $raise(mid, _event.unit, $NULL);
    return;
}


// Entry point
procedure {:entrypoint} Main();
  modifies $CurrMid, $MType, $Heap, $State, $IsHalted, $Raised, $Inbox, $Payload;

implementation {:entrypoint} Main()
{
  var m: int;

  $main:
    call m := $create_machine(_machine.server, $NULL);
    return;
}
