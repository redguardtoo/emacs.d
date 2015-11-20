"""Python 2/3 compatibility definitions.

These are used by the rest of Elpy to keep compatibility definitions
in one place.

"""

import sys


if sys.version_info >= (3, 0):
    PYTHON3 = True

    from io import StringIO

    def ensure_not_unicode(obj):
        return obj
else:
    PYTHON3 = False

    from StringIO import StringIO  # noqa

    def ensure_not_unicode(obj):
        """Return obj. If it's a unicode string, convert it to str first.

        Pydoc functions simply don't find anything for unicode
        strings. No idea why.

        """
        if isinstance(obj, unicode):
            return obj.encode("utf-8")
        else:
            return obj
