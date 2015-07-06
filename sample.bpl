// Program
var $MType: [int] Machine;
var $CurrMid: int;

var $Heap: [int, int] int;
var $State: [int] State;
var $Raised: [int] Event;

var $Inbox: [int, int] Event;
var $InboxSize: [int] int;


// Types
type Machine;
type State;
type Fun;
type Event = int;

const unique $HALT: Event;
const unique $DEFAULT: Event;
const unique $NULL: int;


// Machinery
procedure {:inline 1} $create_machine(m: Machine) returns (r: int);
  modifies $CurrMid, $MType, $InboxSize;

implementation {:inline 1} $create_machine(m: Machine) returns (r: int)
{
  var mid: int;

  $bb0:
    assume $CurrMid > 0;
    mid := $CurrMid;
    $CurrMid := $CurrMid + 1;

    $InboxSize[mid] := 0;

    if (m == _machine.server)
    {
      $MType[mid] := _machine.server;
      async call _machine.server.constructor(r);
    }
    else if (m == _machine.client)
    {
      $MType[mid] := _machine.client;
      async call _machine.client.constructor(r);
    }

    r := mid;
    return;
}

procedure {:inline 1} $raise(mid: int, e: Event);
  modifies $State, $Raised, $Inbox, $InboxSize;

implementation {:inline 1} $raise(mid: int, e: Event)
{
  $bb0:
    $Raised[mid] := e;
    call $handle_event(mid);
    return;
}

procedure {:inline 1} $send(mid: int, e: Event);
  modifies $Inbox, $InboxSize;

implementation {:inline 1} $send(mid: int, e: Event)
{
  $bb0:
    call $enqueue(mid, e);
    async call $handle_event(mid);
    return;
}

procedure {:inline 1} $enqueue(mid: int, e: Event);
  modifies $Inbox, $InboxSize;

implementation {:inline 1} $enqueue(mid: int, e: Event)
{
  var index: int;

  $bb0:
    index := $InboxSize[mid];
    $Inbox[mid, index] := e;
    $InboxSize[mid] := $InboxSize[mid] + 1;
    return;
}

procedure {:inline 1} $get_next_event(mid: int) returns (r: Event);
  modifies $Raised;

implementation {:inline 1} $get_next_event(mid: int) returns (r: Event)
{
  $bb0:
    r := $NULL;

    if ($Raised[mid] != $NULL)
    {
      r := $Raised[mid];
      $Raised[mid] := $NULL;
    }
    else if ($InboxSize[mid] > 0)
    {

      // while (true)
      // {
      //   break;
      //   // assert false;
      // }
      assert false;
    }

    return;
}

procedure {:inline 1} $handle_event(mid: int);
  modifies $State, $Raised, $Inbox, $InboxSize;

implementation {:inline 1} $handle_event(mid: int)
{
  var nextEvent: Event;

  $bb0:
    call nextEvent := $get_next_event(mid);

    if ($MType[mid] == _machine.server)
    {
      if ($State[mid] == _machine.server.init)
      {
        if (nextEvent == _event.unit)
        {
          call $goto_state(mid, _machine.server.playing);
        }
      }
      else if ($State[mid] == _machine.server.playing)
      {
        if (nextEvent == _event.unit)
        {

        }
        else if (nextEvent == _event.ping)
        {

        }
      }
    }
    else if ($MType[mid] == _machine.client)
    {
      if ($State[mid] == _machine.client.init)
      {

      }
      else if ($State[mid] == _machine.client.playing)
      {

      }
    }

    return;
}

procedure {:inline 1} $goto_state(mid: int, s: State);
  modifies $State, $Inbox, $InboxSize;

implementation {:inline 1} $goto_state(mid: int, s: State)
{
  $bb0:
    $State[mid] := s;
    if (s == _machine.server.playing)
    {
      call _machine.server.playing.entry(mid);
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

const {:entry} unique _machine.server.init.entry: Fun;
const {:entry} unique _machine.server.playing.entry: Fun;

procedure {:inline 1} _machine.server.constructor(mid: int);
  modifies $CurrMid, $MType, $Heap, $State, $Raised, $Inbox, $InboxSize;

implementation {:inline 1} _machine.server.constructor(mid: int)
{
  $bb0:
    yield;
    $Heap[mid, _machine.server.client] := $NULL;
    $State[mid] := _machine.server.init;
    $Raised[mid] := $NULL;
    call _machine.server.init.entry(mid);
    return;
}

procedure {:inline 1} _machine.server.init.entry(mid: int);
  modifies $CurrMid, $MType, $Heap, $State, $Raised, $Inbox, $InboxSize;

implementation {:inline 1} _machine.server.init.entry(mid: int)
{
  var client: int;

  $bb0:
    call client := $create_machine(_machine.client);
    $Heap[mid, _machine.server.client] := client;
    call $raise(mid, _event.unit);
    return;
}

procedure {:inline 1} _machine.server.playing.entry(mid: int);
  modifies $Inbox, $InboxSize;

implementation {:inline 1} _machine.server.playing.entry(mid: int)
{
  $bb0:
    call $send($Heap[mid, _machine.server.client], _event.pong);
    return;
}

procedure {:inline 1} _machine.server.sendPong(mid: int);
  modifies $Inbox, $InboxSize;

implementation {:inline 1} _machine.server.sendPong(mid: int)
{
  $bb0:
    call $send($Heap[mid, _machine.server.client], _event.pong);
    return;
}


// Machine: client
const unique _machine.client: Machine;
const {:start} unique _machine.client.init: State;
const unique _machine.client.playing: State;

const unique _machine.client.server: int;
const unique _machine.client.counter: int;

const {:entry} unique _machine.client.init.entry: Fun;
const {:entry} unique _machine.client.playing.entry: Fun;

procedure {:inline 1} _machine.client.constructor(mid: int);
  modifies $Heap, $State, $Raised;

implementation {:inline 1} _machine.client.constructor(mid: int)
{
  $bb0:
    yield;
    $Heap[mid, _machine.client.server] := $NULL;
    $Heap[mid, _machine.client.counter] := 0;
    $State[mid] := _machine.client.init;
    $Raised[mid] := $NULL;
    return;
}

procedure {:inline 1} _machine.client.init.entry(mid: int);
  modifies $CurrMid, $MType, $Heap, $State, $Raised;

implementation {:inline 1} _machine.client.init.entry(mid: int)
{
  var client: int;

  $bb0:
    assert false;
    return;
}

procedure {:inline 1} _machine.client.playing.entry(mid: int);

implementation {:inline 1} _machine.client.playing.entry(mid: int)
{
  $bb0:
    return;
}

procedure {:inline 1} _machine.client.sendPing(mid: int);

implementation {:inline 1} _machine.client.sendPing(mid: int)
{
  $bb0:
    return;
}


// Entry point
procedure {:entrypoint} Main();
  modifies $CurrMid, $MType, $InboxSize;

implementation {:entrypoint} Main()
{
  var m: int;

  $main:
    call m := $create_machine(_machine.server);
    return;
}
