class Event
{
  var name: string;
  var payload: object;

  constructor(e: string, p: object)
    modifies this
  {
    this.name := e;
    this.payload := p;
  }
}

trait Machine
{
  var p_state: string;
  var p_inbox: seq<Event>;

  method p_raise(e: Event)
    requires e != null
  {
    print "raising\n";
    this.p_handle_event(e);
  }

  method p_send(m: Machine, e: Event)
    requires m != null
    requires e != null
    modifies m
  {
    print "sending\n";
    m.p_enqueue(e);
  }

  method p_enqueue(e: Event)
    requires e != null
    modifies this
  {
    print "enqueing\n";
    p_inbox := [e] + p_inbox;
    var nextEvent := p_inbox[0];
    p_inbox := p_inbox[1..];
  }

  method p_handle_event(e: Event)
    requires e != null
}

class Server extends Machine
{
  var client: Machine;

  constructor()
    modifies this
  {
    this.client := null;
    this.p_state := "Init";
    this.p_entry_init();
  }

  method p_entry_init()
    modifies this
  {
    print "server entry\n";
    this.client := new Client();
    var e := new Event("unit", null);
    this.p_raise(e);
  }

  method p_entry_playing()
  {
    print "server playing\n";
  }

  method p_handle_event(e: Event)
    requires e != null
  {
    if (this.p_state == "Init")
    {
      if (e.name == "unit")
      {
        this.p_entry_playing();
      }
    }
    else if (this.p_state == "Playing")
    {

    }
  }
}

class Client extends Machine
{
  var server: Machine;

  constructor()
    modifies this
  {
    server := null;
    this.p_state := "Init";
    this.p_entry_init();
  }

  method p_entry_init()
  {
    print "client entry\n";
    var e := new Event("unit", null);
    this.p_raise(e);
  }

  method p_entry_playing()
  {
    print "client playing\n";
  }

  method p_handle_event(e: Event)
    requires e != null
  {
    if (this.p_state == "Init")
    {
      if (e.name == "unit")
      {
        this.p_entry_playing();
      }
    }
    else if (this.p_state == "Playing")
    {

    }
  }
}

method Main()
{
  var m := new Server();
}
