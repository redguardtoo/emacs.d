"""A simple JSON-RPC-like server.

The server will read and write lines of JSON-encoded method calls and
responses.

See the documentation of the JSONRPCServer class for further details.

"""

import json
import sys
import traceback


class JSONRPCServer(object):
    """Simple JSON-RPC-like server.

    This class will read single-line JSON expressions from stdin,
    decode them, and pass them to a handler. Return values from the
    handler will be JSON-encoded and written to stdout.

    To implement a handler, you need to subclass this class and add
    methods starting with "rpc_". Methods then will be found.

    Method calls should be encoded like this:

    {"id": 23, "method": "method_name", "params": ["foo", "bar"]}

    This will call self.rpc_method("foo", "bar").

    Responses will be encoded like this:

    {"id": 23, "result": "foo"}

    Errors will be encoded like this:

    {"id": 23, "error": "Simple error message"}

    See http://www.jsonrpc.org/ for the inspiration of the protocol.

    """

    def __init__(self, stdin=None, stdout=None):
        """Return a new JSON-RPC server object.

        It will read lines of JSON data from stdin, and write the
        responses to stdout.

        """
        if stdin is None:
            self.stdin = sys.stdin
        else:
            self.stdin = stdin
        if stdout is None:
            self.stdout = sys.stdout
        else:
            self.stdout = stdout

    def read_json(self):
        """Read a single line and decode it as JSON.

        Can raise an EOFError() when the input source was closed.

        """
        line = self.stdin.readline()
        if line == '':
            raise EOFError()
        return json.loads(line)

    def write_json(self, **kwargs):
        """Write an JSON object on a single line.

        The keyword arguments are interpreted as a single JSON object.
        It's not possible with this method to write non-objects.

        """
        self.stdout.write(json.dumps(kwargs) + "\n")
        self.stdout.flush()

    def handle_request(self):
        """Handle a single JSON-RPC request.

        Read a request, call the appropriate handler method, and
        return the encoded result. Errors in the handler method are
        caught and encoded as error objects. Errors in the decoding
        phase are not caught, as we can not respond with an error
        response to them.

        """
        request = self.read_json()
        if 'method' not in request:
            raise ValueError("Received a bad request: {0}"
                             .format(request))
        method_name = request['method']
        request_id = request.get('id', None)
        params = request.get('params') or []
        try:
            method = getattr(self, "rpc_" + method_name, None)
            if method is not None:
                result = method(*params)
            else:
                result = self.handle(method_name, params)
            if request_id is not None:
                self.write_json(result=result,
                                id=request_id)
        except Fault as fault:
            error = {"message": fault.message,
                     "code": fault.code}
            if fault.data is not None:
                error["data"] = fault.data
            self.write_json(error=error, id=request_id)
        except Exception as e:
            error = {"message": str(e),
                     "code": 500,
                     "data": {"traceback": traceback.format_exc()}}
            self.write_json(error=error, id=request_id)

    def handle(self, method_name, args):
        """Handle the call to method_name.

        You should overwrite this method in a subclass.
        """
        raise Fault("Unknown method {0}".format(method_name))

    def serve_forever(self):
        """Serve requests forever.

        Errors are not caught, so this is a slight misnomer.

        """
        while True:
            try:
                self.handle_request()
            except (KeyboardInterrupt, EOFError, SystemExit):
                break


class Fault(Exception):
    """RPC Fault instances.

    code defines the severity of the warning.

    2xx: Normal behavior lead to end of operation, i.e. a warning
    4xx: An expected error occurred
    5xx: An unexpected error occurred (usually includes a traceback)
    """
    def __init__(self, message, code=500, data=None):
        super(Fault, self).__init__(message)
        self.message = message
        self.code = code
        self.data = data
