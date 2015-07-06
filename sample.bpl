// Program
var $M: [Machine] Machine;

//var $Heap: <T>[int, Field T] T;
var $Heap: [int, int] int;
//var $State: [int] State;
var $State: [int] int;
var $CurrMid: int;

const unique $NULL: int;
axiom $NULL == 0;


// Types
type Event;
type Machine;
//type State;
//type Field _;
type Fun;

// Machinery
procedure {:inline 1} $create_machine(m: Machine) returns (r: int);
  modifies $CurrMid;

implementation {:inline 1} $create_machine(m: Machine) returns (r: int)
{
  $bb0:
    assume $CurrMid > 0;
    r := $CurrMid;
    $CurrMid := $CurrMid + 1;

    if (m == _machine.server)
    {
      async call _machine.server.constructor(r);
    }
    else if (m == _machine.client)
    {
      async call _machine.client.constructor(r);
    }
    return;
}

procedure {:inline 1} $raise(mid: int);

implementation {:inline 1} $raise(mid: int)
{
  $bb0:
    assert false;
    return;
}

// Events
const unique _event.ping: Event;
const unique _event.pong: Event;
const unique _event.unit: Event;


// Machine: server
const {:main} unique _machine.server: Machine;
const {:start} unique _machine.server.init: int;
const unique _machine.server.playing: int;

//const unique _machine.server.client: Field int;
const unique _machine.server.client: int;

const {:entry} unique _machine.server.init.entry: Fun;
const {:entry} unique _machine.server.playing.entry: Fun;

procedure {:inline 1} _machine.server.constructor(mid: int);
  modifies $CurrMid, $Heap, $State;

implementation {:inline 1} _machine.server.constructor(mid: int)
{
  $bb0:
    yield;
    $Heap[mid, _machine.server.client] := $NULL;
    $State[mid] := _machine.server.init;
    call _machine.server.init.entry(mid);
    return;
}

procedure {:inline 1} _machine.server.init.entry(mid: int);
  modifies $CurrMid, $Heap, $State;

implementation {:inline 1} _machine.server.init.entry(mid: int)
{
  var client: int;

  $bb0:
    call {:create} client := $create_machine(_machine.client);
    $Heap[mid, _machine.server.client] := client;
    call {:raise} $raise(mid);
    return;
}


// Machine: client
const unique _machine.client: Machine;
const {:start} unique _machine.client.init: int;
const unique _machine.client.playing: int;

//const unique _machine.client.server: Field int;
const unique _machine.client.server: int;

const {:entry} unique _machine.client.init.entry: Fun;
const {:entry} unique _machine.client.playing.entry: Fun;

procedure {:inline 1} _machine.client.constructor(mid: int);
  modifies $Heap, $State;

implementation {:inline 1} _machine.client.constructor(mid: int)
{
  $bb0:
    yield;
    $Heap[mid, _machine.client.server] := $NULL;
    $State[mid] := _machine.client.init;
    return;
}


// Entry point
procedure {:entrypoint} Main();
  modifies $CurrMid;

implementation {:entrypoint} Main()
{
  var m: int;

  $main:
    call {:create} m := $create_machine(_machine.server);
    return;
}
