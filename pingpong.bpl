// Program
var $CurrMid: int;
var $Inbox: [int][int]Event;
var $InboxSize: [int]int;
var $Payload: [int]Payload;

var {:thread_local} $Heap: [int][int]int;
var {:thread_local} $State: [int]State;
var {:thread_local} $IsHalted: [int]bool;
var {:thread_local} $Raised: [int]Event;
var {:thread_local} $Ignores: [int][Event]bool;
var {:thread_local} $Defers: [int][Event]bool;


// Types
type Machine;
type State;
type Event;
type Payload = int;

const unique $DEFAULT: Event;
const unique $HALT: Event;

const unique $NULL: int;
axiom $NULL == 0;


// Machinery
procedure {:inline 1} $create_machine(m: Machine, p: Payload) returns (r: int);
  modifies $CurrMid, $Heap, $State, $IsHalted, $InboxSize, $Payload;

implementation {:inline 1} $create_machine(m: Machine, p: Payload) returns (mid: int)
{
  $bb0:
    mid := $CurrMid;
    $CurrMid := $CurrMid + 1;

    $InboxSize[mid] := 0;
    $Payload[mid] := p;

    if (m == _machine.server)
    {
      async call _machine.server.constructor(mid);
    }
    else if (m == _machine.client)
    {
      async call _machine.client.constructor(mid);
    }

    return;
}

procedure {:inline 1} $raise(mid: int, e: Event, p: Payload);
  modifies $Heap, $State, $IsHalted, $Inbox, $InboxSize, $Payload;

implementation {:inline 1} $raise(mid: int, e: Event, p: Payload)
{
  $bb0:
    $Payload[mid] := p;
    $Raised[mid] := e;
    return;
}

procedure {:inline 1} $send(mid: int, e: Event, p: Payload);
  modifies $Inbox, $InboxSize, $Payload;

implementation {:inline 1} $send(mid: int, e: Event, p: Payload)
{
  var index: int;

  $bb0:
    index := $InboxSize[mid];
    $Inbox[mid][index] := e;
    $InboxSize[mid] := $InboxSize[mid] + 1;
    $Payload[mid] := p;
    return;
}

procedure {:inline 1} $q_remove(mid: int, idx: int);
  modifies $Inbox, $InboxSize;

implementation {:inline 1} $q_remove(mid: int, idx: int)
{
  var index: int;

  $bb0:
    index := idx;

    while (index < $InboxSize[mid] - 1)
    {
      $Inbox[mid][index] := $Inbox[mid][index + 1];
      index := index + 1;
    }

    $InboxSize[mid] := $InboxSize[mid] - 1;

    return;
}

procedure {:inline 1} $run_event_handler(mid: int, mtype: Machine);
  modifies $Heap, $State, $IsHalted, $Inbox, $InboxSize, $Payload;

implementation {:inline 1} $run_event_handler(mid: int, mtype: Machine)
{
  var nextEvent: Event;

  $bb0:
    nextEvent := $DEFAULT;
    while (!$IsHalted[mid])
    {
      call nextEvent := $get_next_event(mid);
      if (nextEvent == $DEFAULT)
      {
        assume false;
      }
      else if (nextEvent == $HALT)
      {
        $IsHalted[mid] := true;
        break;
      }

      if (mtype == _machine.server)
      {
        call _machine.server.handle_event(mid, nextEvent);
      }
      else if (mtype == _machine.client)
      {
        call _machine.client.handle_event(mid, nextEvent);
      }
    }

    return;
}

procedure {:inline 1} $get_next_event(mid: int) returns (r: Event);
  modifies $Inbox, $InboxSize;

implementation {:inline 1} $get_next_event(mid: int) returns (r: Event)
{
  var nextEvent: Event;
  var index: int;
  var inbox: [int] Event;
  var size: int;

  $bb0:
    nextEvent := $DEFAULT;

    index := 0;
    if ($Raised[mid] != $DEFAULT)
    {
      nextEvent := $Raised[mid];
      $Raised[mid] := $DEFAULT;
    }
    else
    {
      yield;
      while (index < $InboxSize[mid])
      {
        if ($Ignores[mid][$Inbox[mid][index]])
        {
          call $q_remove(mid, index);
          index := index - 1;
        }
        else if (!$Defers[mid][$Inbox[mid][index]])
        {
          nextEvent := $Inbox[mid][index];
          call $q_remove(mid, index);
          break;
        }

        index := index + 1;
      }
    }

    r := nextEvent;
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
  modifies $Heap, $State, $IsHalted, $InboxSize;

implementation {:inline 1} _machine.server.constructor(mid: int)
{
  $bb0:
    $IsHalted[mid] := false;
    $State[mid] := _machine.server.init;
    $Heap[mid][_machine.server.client] := $NULL;

    assume (forall e:Event :: $Ignores[mid][e] == false);
    assume (forall e:Event :: $Defers[mid][e] == false);

    call _machine.server.init.entry(mid);
    call $run_event_handler(mid, _machine.server);
    return;
}

procedure {:inline 1} _machine.server.handle_event(mid: int, e: Event);
  modifies $State, $Inbox, $InboxSize, $Payload;

implementation {:inline 1} _machine.server.handle_event(mid: int, e: Event)
{
  $bb0:
    if ($State[mid] == _machine.server.init)
    {
      if (e == _event.unit)
      {
        $State[mid] := _machine.server.playing;
        call _machine.server.playing.entry(mid);
      }
      else
      {
        assert false;
      }
    }
    else if ($State[mid] == _machine.server.playing)
    {
      if (e == _event.ping)
      {
        call _machine.server.sendPong(mid);
      }
      else
      {
        assert false;
      }
    }

    return;
}

procedure {:inline 1} {:entry} _machine.server.init.entry(mid: int);
  modifies $CurrMid, $IsHalted, $Heap, $State, $Inbox, $InboxSize, $Payload;

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
  modifies $Inbox, $InboxSize, $Payload;

implementation {:inline 1} {:entry} _machine.server.playing.entry(mid: int)
{
  $bb0:
    call $send($Heap[mid][_machine.server.client], _event.pong, $NULL);
    return;
}

procedure {:inline 1} _machine.server.sendPong(mid: int);
  modifies $Inbox, $InboxSize, $Payload;

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
  modifies $Heap, $State, $IsHalted, $InboxSize;

implementation {:inline 1} _machine.client.constructor(mid: int)
{
  $bb0:
    $IsHalted[mid] := false;
    $State[mid] := _machine.client.init;
    $Heap[mid][_machine.client.server] := $NULL;
    $Heap[mid][_machine.client.counter] := 0;

    assume (forall e:Event :: $Ignores[mid][e] == false);
    assume (forall e:Event :: $Defers[mid][e] == false);

    call _machine.client.init.entry(mid);
    call $run_event_handler(mid, _machine.client);
    return;
}

procedure {:inline 1} _machine.client.handle_event(mid: int, e: Event);
  modifies $Heap, $State, $IsHalted, $Inbox, $InboxSize, $Payload;

implementation {:inline 1} _machine.client.handle_event(mid: int, e: Event)
{
  $bb0:
    if ($State[mid] == _machine.client.init)
    {
      if (e == _event.unit)
      {
        $State[mid] := _machine.client.playing;
        call _machine.client.playing.entry(mid);
      }
      else
      {
        assert false;
      }
    }
    else if ($State[mid] == _machine.client.playing)
    {
      if (e == _event.unit)
      {
        call _machine.client.playing.entry(mid);
      }
      else if (e == _event.pong)
      {
        call _machine.client.sendPing(mid);
      }
      else
      {
        assert false;
      }
    }

    return;
}

procedure {:inline 1} {:entry} _machine.client.init.entry(mid: int);
  modifies $CurrMid, $Heap, $State, $IsHalted, $Inbox, $InboxSize, $Payload;

implementation {:inline 1} {:entry} _machine.client.init.entry(mid: int)
{
  var client: int;

  $bb0:
    $Heap[mid][_machine.client.server] := $Payload[mid];
    call $raise(mid, _event.unit, $NULL);
    return;
}

procedure {:inline 1} {:entry} _machine.client.playing.entry(mid: int);
  modifies $Heap, $State, $IsHalted, $Inbox, $InboxSize, $Payload;

implementation {:inline 1} {:entry} _machine.client.playing.entry(mid: int)
{
  $bb0:
    if ($Heap[mid][_machine.client.counter] == 1)
    {
      assert false;
      call $raise(mid, $HALT, $NULL);
    }

    return;
}

procedure {:inline 1} _machine.client.sendPing(mid: int);
  modifies $Heap, $State, $IsHalted, $Inbox, $InboxSize, $Payload;

implementation {:inline 1} _machine.client.sendPing(mid: int)
{
  $bb0:
    $Heap[mid][_machine.client.counter] := $Heap[mid][_machine.client.counter] + 1;
    call $send($Heap[mid][_machine.client.server], _event.ping, $NULL);
    call $raise(mid, _event.unit, $NULL);
    return;
}


// Entry point
procedure {:entrypoint} Main();
  modifies $CurrMid, $Heap, $State, $IsHalted, $InboxSize, $Payload;

implementation {:entrypoint} Main()
{
  var m: int;

  $main:
    assume $CurrMid > 0;
    call m := $create_machine(_machine.server, $NULL);
    return;
}
