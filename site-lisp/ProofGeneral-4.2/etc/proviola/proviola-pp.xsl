<?xml version="1.0" encoding="ISO-8859-1"?>

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
    var plains = new Array();
    var obligations = new Array();

    function mouseover(id) {
      plain = getPlain(id);
      obligation = getObligation(id);
      setResponse(plain, obligation);
    };

    function set_array() {
      <xsl:for-each select="movie/film/frame">
        i = <xsl:value-of select="@frameNumber"/>;
        plains[i] ="";
        obligations[i] = "";
        <xsl:for-each select="response-pp/part">
          <xsl:if test="@class = 'plain'">
            plains[i] = "<xsl:value-of select="translate(., '&#x0A;', '&#x09;')"/>";
          </xsl:if>
          <xsl:if test="@class = 'obligation'">

            obligations[i] ="<xsl:value-of select="translate(., '&#x0A;', '&#x09;')"/>";
          </xsl:if>
        </xsl:for-each>
      </xsl:for-each>
    };

    function getPlain(id) {
      return plains[id];
    };
 
    function getObligation(id) {
      return obligations[id];
    };
  
    function setResponse(plain, obligation) {

      goalSpans =  document.getElementById("goal").getElementsByTagName("span");

       goalSpans[0].innerHTML = plain.replace(/&#x09;/g, '\n');
       goalSpans[1].innerHTML = obligation.replace(/&#x09;/g, '\n');
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
        
        <xsl:for-each select="command-pp/part">
          <span>
          <xsl:attribute name="class">
            <xsl:value-of select="@class"/>
          </xsl:attribute>
          <xsl:value-of select="."/>
          </span>
        </xsl:for-each>
          
      </span>
    </xsl:for-each>
    </pre>
    </div>

    <div id="goal" class="goal">
    <pre>
        <span class="context">
        </span>
        <span class="obligation">
        </span>
      </pre>
    </div>
  </body>
  </html>
</xsl:template>
</xsl:stylesheet>
