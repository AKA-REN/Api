--// Network Library

local ReplicatedStorage = game:GetService("ReplicatedStorage")
local Workspace = game:GetService("Workspace")

--// Types
type Connection = RBXScriptConnection
type Remote = RemoteEvent | RemoteFunction | UnreliableRemoteEvent
type Cache = {
	connections: { Connection },
	callbacks: { [RemoteFunction]: (...any) -> ...any },
	remotes: { [string | Instance]: Remote },
}

--// Module
local network = {}
network.__index = network
network.cache = {
	connections = {},
	callbacks = {},
	remotes = {},
} :: Cache

--// Private
local function resolve(name: string | Instance): Remote?
	local cached = network.cache.remotes[name]
	if cached then
		return cached
	end

	if typeof(name) == "Instance" then
		network.cache.remotes[name] = name
		return name
	end

	local remote = ReplicatedStorage:FindFirstChild(name, true) or Workspace:FindFirstChild(name, true)

	if remote then
		network.cache.remotes[name] = remote
	end

	return remote
end

local function isEvent(remote: Remote): boolean
	return remote:IsA("RemoteEvent") or remote:IsA("UnreliableRemoteEvent")
end

local function isFunction(remote: Remote): boolean
	return remote:IsA("RemoteFunction")
end

--// Public
function network:Retrieve(name: string | Instance, func: (...any) -> ()): Connection?
	local remote = resolve(name)

	if not remote then
		return warn("[Network] Remote not found:", name)
	end

	if isEvent(remote) then
		local connection = remote.OnClientEvent:Connect(func)
		table.insert(self.cache.connections, connection)
		return connection
	end

	if isFunction(remote) then
		remote.OnClientInvoke = func
		self.cache.callbacks[remote] = func
		return
	end

	warn("[Network] Unsupported class:", remote.ClassName)
end

function network:Send(name: string | Instance, ...: any): ...any
	local remote = resolve(name)

	if not remote then
		return warn("[Network] Remote not found:", name)
	end

	if isEvent(remote) then
		return remote:FireServer(...)
	end

	if isFunction(remote) then
		return remote:InvokeServer(...)
	end

	warn("[Network] Unsupported class:", remote.ClassName)
end

function network:ClearConnections()
	for i = #self.cache.connections, 1, -1 do
		local conn = self.cache.connections[i]
		if conn.Connected then
			conn:Disconnect()
		end
		self.cache.connections[i] = nil
	end

	for remote in self.cache.callbacks do
		remote.OnClientInvoke = nil
	end
	table.clear(self.cache.callbacks)
end

function network:Destroy()
	self:ClearConnections()
	table.clear(self.cache.remotes)
end

--// Init
getgenv().network = getgenv().network or network
return getgenv().network
