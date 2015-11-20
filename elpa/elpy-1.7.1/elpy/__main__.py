"""Main interface to the RPC server.

You should be able to just run the following to use this module:

python -m elpy

The first line should be "elpy-rpc ready". If it isn't, something
broke.

"""

import sys

import elpy
from elpy.server import ElpyRPCServer

if __name__ == '__main__':
    # Workaround for libraries writing to stderr while they should
    # not. See #458. Can be removed once #461 is implemented.
    import os
    sys.stderr = open(os.devnull)
    # End workaround
    sys.stdout.write('elpy-rpc ready ({0})\n'
                     .format(elpy.__version__))
    sys.stdout.flush()
    ElpyRPCServer().serve_forever()
