if getgenv().network then return getgenv().network end

local findFirstChild = game.FindFirstChild
local isA = game.IsA

local connections = {}
local remoteCache = {}

local function resolveRemote(name)
    local cached = remoteCache[name]
    if cached then return cached end
    if typeof(name) == "Instance" then
        remoteCache[name] = name
        return name
    end
    local found = findFirstChild(game, name, true)
    if found then remoteCache[name] = found end
    return found
end

local function clearConnections()
    for i = #connections, 1, -1 do
        local conn = connections[i]
        if typeof(conn) == "RBXScriptConnection" then
            conn:Disconnect()
        end
        connections[i] = nil
    end
end

getgenv().network = {
    cache = {
        connections = connections,
        remotes = remoteCache,
        clear = clearConnections,
    },

    Retrieve = function(self, name, func)
        local remote = resolveRemote(name)
        if not remote then return warn("Unable to Identify Remote Network") end

        local ok, err = pcall(function()
            if isA(remote, "RemoteEvent") then
                connections[#connections + 1] = remote.OnClientEvent:Connect(func)
            elseif isA(remote, "RemoteFunction") then
                remote.OnClientInvoke = func
            else
                warn("Unable to Connect Network")
            end
        end)

        if not ok then warn("Retrieve Error:", err) end
    end,

    Send = function(self, name, ...)
        local remote = resolveRemote(name)
        if not remote then return warn("Unable to Identify Remote Network") end

        local ok, result = pcall(function(...)
            if isA(remote, "RemoteEvent") then
                return remote:FireServer(...)
            elseif isA(remote, "RemoteFunction") then
                return remote:InvokeServer(...)
            else
                warn("Unable to Connect Network")
            end
        end, ...)

        if ok then return result end
        warn("Send Error:", result)
    end,

    Destroy = function(self)
        clearConnections()
        table.clear(remoteCache)
        getgenv().network = nil
    end,
}

return getgenv().network
