/**
 * Licensed to the Apache Software Foundation (ASF) under one or more
 * contributor license agreements.  See the NOTICE file distributed with
 * this work for additional information regarding copyright ownership.
 * The ASF licenses this file to You under the Apache License, Version 2.0
 * (the "License"); you may not use this file except in compliance with
 * the License.  You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

package org.apache.geronimo.javamail.store.imap.connection;

import java.io.UnsupportedEncodingException;
import java.util.ArrayList;
import java.util.Date;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;

import javax.mail.MessagingException;
import javax.mail.Part;
import javax.mail.internet.ContentDisposition;
import javax.mail.internet.ContentType;
import javax.mail.internet.MimeUtility;


public class IMAPBodyStructure extends IMAPFetchDataItem {

    // the MIME type information
    public ContentType mimeType = new ContentType();
    // the content disposition info
    public ContentDisposition disposition = null;
    // the message ID
    public String contentID;
    public String contentDescription;
    public String transferEncoding;
    // size of the message 
    public int bodySize;
    // number of lines, which only applies to text types.
    public int lines = -1;

    // "parts is parts".  If this is a multipart message, we have a body structure item for each subpart.
    public IMAPBodyStructure[] parts;
    // optional dispostiion parameters
    public Map dispositionParameters;
    // language parameters
    public List languages;
    // the MD5 hash
    public String md5Hash;

    // references to nested message information.
    public IMAPEnvelope nestedEnvelope;
    public IMAPBodyStructure nestedBody;


    public IMAPBodyStructure(IMAPResponseTokenizer source) throws MessagingException {
        super(BODYSTRUCTURE);
        parseBodyStructure(source);
    }


    protected void parseBodyStructure(IMAPResponseTokenizer source) throws MessagingException {
        // the body structure needs to start with a left paren
        source.checkLeftParen();

        // if we start with a parentized item, we have a multipart content type.  We need to
        // recurse on each of those as appropriate
        if (source.peek().getType() == '(') {
            parseMultipartBodyStructure(source);
        }
        else {
            parseSinglepartBodyStructure(source);
        }
    }


    protected void parseMultipartBodyStructure(IMAPResponseTokenizer source) throws MessagingException {
        mimeType.setPrimaryType("multipart");
        ArrayList partList = new ArrayList();

        do {
            // parse the subpiece (which might also be a multipart).
            IMAPBodyStructure part = new IMAPBodyStructure(source);
            partList.add(part);
            // we keep doing this as long as we seen parenthized items.
        } while (source.peek().getType() == '(');
        
        parts = (IMAPBodyStructure[])partList.toArray(new IMAPBodyStructure[partList.size()]); 

        // get the subtype (required)
        mimeType.setSubType(source.readString());

        if (source.checkListEnd()) {
            return;
        }
        // if the next token is the list terminator, we're done.  Otherwise, we need to read extension
        // data.
        if (source.checkListEnd()) {
            return;
        }
        // read the content parameter information and copy into the ContentType.
        mimeType.setParameterList(source.readParameterList());

        // more optional stuff
        if (source.checkListEnd()) {
            return;
        }

        // go parse the extensions that are common to both single- and multi-part messages.
        parseMessageExtensions(source);
    }


    protected void parseSinglepartBodyStructure(IMAPResponseTokenizer source) throws MessagingException {
        // get the primary and secondary types.
        mimeType.setPrimaryType(source.readString());
        mimeType.setSubType(source.readString());

        // read the parameters associated with the content type.
        mimeType.setParameterList(source.readParameterList());

        // now a bunch of string value parameters
        contentID = source.readStringOrNil();
        contentDescription = source.readStringOrNil();
        transferEncoding = source.readStringOrNil();
        bodySize = source.readInteger();

        // is this an embedded message type?  Embedded messages include envelope and body structure
        // information for the embedded message next.
        //add condition source.peek().getType() == '(' to fix bug 76
        if (mimeType.match("message/rfc822") && source.peek().getType() == '(') {
            // parse the nested information
            nestedEnvelope = new IMAPEnvelope(source);
            nestedBody = new IMAPBodyStructure(source);
            lines = source.readInteger();
        }
        // text types include a line count
        else if (mimeType.match("text/*")) {
            lines = source.readInteger();
        }

        // now the optional extension data.  All of these are optional, but must be in the specified order.
        if (source.checkListEnd()) {
            return;
        }

        md5Hash = source.readString();

        // go parse the extensions that are common to both single- and multi-part messages.
        parseMessageExtensions(source);
    }

    /**
     * Parse common message extension information shared between
     * single part and multi part messages.
     *
     * @param source The source tokenizer..
     */
    protected void parseMessageExtensions(IMAPResponseTokenizer source) throws MessagingException {

        // now the optional extension data.  All of these are optional, but must be in the specified order.
        if (source.checkListEnd()) {
            return;
        }

        disposition = new ContentDisposition();
        // now the dispostion.  This is a string, followed by a parameter list.
        boolean dispoFlag = false;
        if(source.peek().getType() == '(')//fix the problem that disposition is parenthesized
        {
        	source.next();
        	dispoFlag = true;
	        disposition.setDisposition(source.readString());
	        //fix bug 157, there's no word after disposition.
	        if(!dispoFlag && source.checkListEnd())
	        	return;
	        disposition.setParameterList(source.readParameterList());
	        //skip the corresponding ')'
	        if(dispoFlag)
	        	source.next();
        }
        else
        	disposition.setDisposition(source.readString());
        // once more
        if (source.checkListEnd()) {
            return;
        }
        // read the language info.
        if(source.peek().getType() == '(')//fix the problem that disposition is parenthesized
        {
        	languages = source.readStringList();
        	source.next();
        }
        else
        {
        	String lang = source.readStringOrNil();
        	if(lang != null)
        	{
        		if(languages == null)
        			languages = new ArrayList<String>();
        		languages.add(lang);
        	}
        }
        
        // next is the body location information.  The Javamail APIs don't really expose that, so
        // we'll just skip over that.

        // once more
        if (source.checkListEnd()) {
            return;
        }
        // read the location info.
        source.readStringList();


        // we don't recognize any other forms of extension, so just skip over these.
        while (source.notListEnd()) {
            source.skipExtensionItem();
        }
        source.checkListEnd();
    }


    /**
     * Tests if a body structure is for a multipart body.
     *
     * @return true if this is a multipart body part, false for a single part.
     */
    public boolean isMultipart() {
        return parts != null;
    }
    
    
    /**
     * Test if this body structure represents an attached message.  If it's a
     * message, this will be a single part of MIME type message/rfc822. 
     * 
     * @return True if this is a nested message type, false for either a multipart or 
     *         a single part of another type.
     */
    public boolean isAttachedMessage() {
        return !isMultipart() && mimeType.match("message/rfc822"); 
    }
    
    /**
     * Tim Liu add this function at 09/17/2011 
     * recursively check whether this body structure has attachment.
     */
    public boolean hasAttachment()
    {
    	if(isMultipart())
    	{
    		for(int i = 0; i < this.parts.length; i++)
    		{
    			if(parts[i].hasAttachment())
    				return true;
    		}
    	}
    	else//simple part
    	{
    		String disp = disposition.getDisposition();
    		if(disp == null || disp.equals("NIL"))
    		{
    			//for qq imap server,bug 401.
    			//APPLICATION/OCTET-STREAM; charset=gb18030; name=viemu.txt
    			//test sending some other type of attachment, such as zip,docx, the content type is also /APPLICATION/OCTET-STREAM
    			if(mimeType.match("APPLICATION/OCTET-STREAM"))
    			{
    				 String fileName = mimeType.getParameter("name");
    				 return fileName!=null&&!fileName.isEmpty();
    			}
    			else
    				return false;
    		}
    		 if (disp.equalsIgnoreCase(Part.ATTACHMENT))
    			 return true;
    		 //some attachment is marked as "INLINE'
    		 if(disp.equalsIgnoreCase(Part.INLINE))
    		 {
    			 String fileName = disposition.getParameter("filename");
    			 if(fileName == null || fileName.equals(""))
    				 return false;
				try
				{
					String decoded = MimeUtility.decodeText(fileName);
					if (decoded != null && !decoded.equals(""))
						return true;
				}
				catch (UnsupportedEncodingException exp)
				{
					exp.printStackTrace();
					return false;
				}
    		 }
    	}
    	return false;
    }
    
    /**
     * Tim Liu add this function at 09/17/2011 
     * recursively check whether this body structure has attachment.
     */
    public LinkedList<String> getAttachmentNames()
    {
    	LinkedList<String> fiNames = new LinkedList<String>();
    	if(isMultipart())
    	{
    		for(int i = 0; i < this.parts.length; i++)
    			fiNames.addAll(parts[i].getAttachmentNames());;
    	}
    	else//simple part
    	{
    		String disp = disposition.getDisposition();
    		if(disp == null|| disp.equals("NIL"))
    		{
    			//for qq imap server,bug 401.
    			//APPLICATION/OCTET-STREAM; charset=gb18030; name=viemu.txt
    			//test sending some other type of attachment, such as zip,docx, the content type is also /APPLICATION/OCTET-STREAM
    			if(mimeType.match("APPLICATION/OCTET-STREAM"))
    			{
    				 String fileName = mimeType.getParameter("name");
    				 if(fileName!=null&&!fileName.isEmpty())
    					 fiNames.add(fileName);
    			}
    			return fiNames;
    		}
    		 if (disp.equalsIgnoreCase(Part.ATTACHMENT))
    		 {
    			 String fileName=null;
    			 String nameFromDisposition = disposition.getParameter("filename");
    			 String nameFormContentType=mimeType.getParameter("name");
    			 if((nameFromDisposition == null || nameFromDisposition.equals(""))&&(nameFormContentType == null || nameFormContentType.equals("")))
    				  fiNames.add("");
    			 else
    			 {
    				fileName=nameFromDisposition == null || nameFromDisposition.equals("")?nameFormContentType:nameFromDisposition;
					try
					{
						String decoded = MimeUtility.decodeText(fileName);
						if (decoded != null && !decoded.equals(""))
							fiNames.add(decoded);
						else
							fiNames.add("");
					}
					catch (UnsupportedEncodingException exp)
					{
						exp.printStackTrace();
						return fiNames;
					}
    			 }
    			 return fiNames;
    		 }
    		 //some attachment is marked as "INLINE'
    		 if(disp.equalsIgnoreCase(Part.INLINE))
    		 {
    			 String fileName=null;
    			 String nameFromDisposition = disposition.getParameter("filename");
    			 String nameFormContentType=mimeType.getParameter("name");
    			 if((nameFromDisposition == null || nameFromDisposition.equals(""))&&(nameFormContentType == null || nameFormContentType.equals("")))
    				 return fiNames;
    			fileName=nameFromDisposition == null || nameFromDisposition.equals("")?nameFormContentType:nameFromDisposition;
				try
				{
					String decoded = MimeUtility.decodeText(fileName);
					if (decoded != null && !decoded.equals(""))
					{
						fiNames.add(decoded);
						return fiNames;
					}
				}
				catch (UnsupportedEncodingException exp)
				{
					exp.printStackTrace();
					return fiNames;
				}
    		 }
    	}
    	return fiNames;
    }
}

