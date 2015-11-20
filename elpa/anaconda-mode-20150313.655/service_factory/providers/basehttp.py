"""
    service_factory.providers.basehttp
    ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

    This module define service provider based on the BaseHTTPHandler.

    :copyright: (c) 2015 by Artem Malyshev.
    :license: GPL3, see LICENSE for more details.
"""

from __future__ import (
    absolute_import, unicode_literals, division, print_function)

import socket
import sys
from traceback import print_exc

from six.moves.BaseHTTPServer import BaseHTTPRequestHandler, HTTPServer

from service_factory.errors import parse_error
from service_factory.exceptions import ServiceException


class HTTPRequestHandler(BaseHTTPRequestHandler):

    protocol_version = 'HTTP/1.1'
    error_message_format = ''

    def log_request(self, *args):
        """Ignore non error logging messages."""

        pass

    def do_POST(self):
        try:
            content_len = self.headers.get('content-length')
            if content_len and content_len.isdigit():
                raw_data = self.rfile.read(int(content_len))
                data = raw_data.decode('utf-8')
                status, response = self.server.service(data)
            else:
                parse_error()
        except ServiceException as error:
            self.log_error('=' * 80)
            print_exc()
            status, response = error.args

        response = response.encode('utf-8')
        self.send_response(status)
        self.send_header("Content-Length", len(response))
        self.end_headers()
        self.wfile.write(response)


class HTTPServiceProvider(HTTPServer):
    """Base HTTP service provider."""

    def __init__(self, service, host, port,
                 report_message='service factory port {port}'):

        self.service = service
        self.host = host
        self.port = port
        self.report_message = report_message
        self.bind()

    def bind(self):
        """Bind and activate HTTP server."""

        if self.port != 'auto':
            self.do_bind()
        else:
            self.port = 9000
            while True:
                try:
                    self.do_bind()
                except (OSError, socket.error):
                    self.port += 1
                else:
                    break
            self.report()

    def do_bind(self):
        """Perform HTTP server binding and activation."""

        HTTPServer.__init__(self, (self.host, self.port), HTTPRequestHandler)

    def report(self):
        """Report startup info to stdout."""

        print(self.report_message.format(
            service=self.service,
            host=self.host,
            port=self.port))
        sys.stdout.flush()
