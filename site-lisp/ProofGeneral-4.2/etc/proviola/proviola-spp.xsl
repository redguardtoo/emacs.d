<?xml version="1.0" encoding="ISO-8859-1"?>
<!-- Modified form of proviola.xsl, taken from
     http://mws.cs.ru.nl/proviola 2/8/10. -->

<xsl:stylesheet version="1.0"
 xmlns:xsl="http://www.w3.org/1999/XSL/Transform">


<xsl:template match="/">
  <html>
  <head>
    <style type="text/css">
    body {
      margin: 0px;
      padding: 0px;
    }

    div.commands {
      margin: 0px;
      padding: 0px;
      width: 50%;
    /* border-right: 1px solid #777; */
    }

    span.command:hover {
      background-color: #ccc;
    }

    div.goal {
      position: fixed;
      left: 50%;
      bottom: 0px;
      width: 50%;
      margin: 0px;
      padding-top: 100%;
      border-left: 1px solid #777;
      background-color: #fff;
    }

    div.hidden {
      display: none;
    }

    pre {
      padding: 4px 8px 4px 8px;
      margin: 0px;
      background-color: #fff;
    }

    span.label {
      color: #f00;
    }

    span.comment {
      color: #090;
    }

    span.lemma {
      color: #00f;
    }

    span.obligation {
    /* color: #c40; */
      color: #a0f;
    }
    </style>
  <script type = "text/javascript">
    var responses = new Array();
    
    function mouseover(id) {
      response = get_response(id);
      set_response(response);
    };

    function set_array() {
       <xsl:for-each select="movie/film/frame">
          <xsl:variable name="data">
            <xsl:call-template name="replace">
              <xsl:with-param name="string">
                <xsl:value-of 
                  select="translate(response, '&#x0A;', '&#x09;') "/> 
              </xsl:with-param>
              <xsl:with-param name="from">&quot;</xsl:with-param>
              <xsl:with-param name="to">\"</xsl:with-param>
            </xsl:call-template>
          </xsl:variable>

          i = <xsl:value-of select="@frameNumber"/>;
          data = "<xsl:value-of select="$data"/>";
          responses[i]=data;
        </xsl:for-each>
    };

    function get_response(id) {
      return responses[id];
    };
  
    function set_response(response) {
      goalSpan =  document.getElementById("goal").getElementsByTagName("span")[0];
      goalSpan.innerHTML = response.replace(/&#x09;/g, '\n');
    };
  </script>
  </head>

  <body onload="set_array()">
    <div class = "commands">
    <pre>
    <xsl:for-each select="movie/film/frame">
      <span class ="command">
        <xsl:attribute name="onmouseover">
        mouseover(
          <xsl:value-of select="@frameNumber"/>
        )
        </xsl:attribute>
        <span>
          <xsl:attribute name="class">
	    <xsl:value-of select="command/@class"/>
          </xsl:attribute>
          <xsl:value-of select="command"/>
	</span>
      </span>
    </xsl:for-each>
    </pre>
    </div>

    <div id="goal" class="goal">
    <pre>
        <span>
        </span>
      </pre>
    </div>
  </body>
  </html>
</xsl:template>

<xsl:template name="replace">
<xsl:param name="string"/>
  <xsl:param name="from"/>
  <xsl:param name="to"/>
  <xsl:choose>
    <xsl:when test= "contains($string, $from)">
      <xsl:value-of select="substring-before($string, $from)"/>
        <xsl:value-of select="$to"/>
      <xsl:call-template name="replace">
        <xsl:with-param name="string" 
                        select="substring-after($string, $from)"/>
        <xsl:with-param name="from" select="$from"/>
        <xsl:with-param name="to" select="$to"/>
      </xsl:call-template>
    </xsl:when>
    <xsl:otherwise>
      <xsl:value-of select="$string"/>
    </xsl:otherwise>
  </xsl:choose>
</xsl:template>


</xsl:stylesheet>
